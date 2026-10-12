module

import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Geometry.Rotations.Cayley.Cap
import Purelib.Geometry.Rotations.Reflection
import Purelib.Geometry.Rotations.Basic
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Inverse
public import Purelib.Geometry.Quadratic.Space3.Perpendicular
public import Purelib.Geometry.Rotations.Spread
import Purelib.LinearAlgebra.Coordinates3.Antisymmetric
public import Purelib.LinearAlgebra.Coordinates3.Cayley
public import Purelib.LinearAlgebra.Coordinates3.Projector
import Purelib.LinearAlgebra.Coordinates3.Vector
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

section
public section

/-!
# Rational rotations, section 7: recovering the anchor

The paper's boxed antisymmetric formula is the executable definition of a
rotation's anchor.  An explicit adjugate inverse for `I + ρ` ties that cached
value to the big Cayley transform; downstream proofs use the cached formula
rather than recomputing the inverse.
-/

namespace Purelib.Geometry.Rotations.Axis.Recovery

open Purelib
open Purelib.Algebra.Field
open Purelib.Geometry
open Purelib.Geometry.Quadratic.Space3
open Purelib.Geometry.Rotations
open Purelib.Geometry.Rotations.Cayley
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Coordinates3
open Purelib.LinearAlgebra.Coordinates3.Antisymmetric

variable {K : Type*} [Algebra.Field.ExplicitField K]

/-- Recover the anchor matrix of a rotation that is not a half turn.

The stored formula scales the difference between the rotation matrix and its transpose by the inverse of one plus its
trace (Definition 34 and Theorem 35.5). -/
@[expose] public def rotationAnchor (rotation : Rotations.Basic.Rotation K)
    (_notHalfTurn : Spread.halfSpread rotation ≠ 1) : Coordinates3.Matrix3 K :=
  Matrix3.scale (1 / (1 + Matrix3.trace rotation.matrix))
    (Matrix3.sub rotation.matrix (Matrix3.transpose rotation.matrix))

/-- The unique displayed vector encoded by a rotation's cached anchor. -/
@[expose] public def rotationAnchorVector (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1) : Coordinates3.Vector K :=
  Antisymmetric.anchorVector (Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn)

/-- The trace denominator is four times the complementary half spread. -/
theorem one_add_trace_eq_four_mul_one_sub_halfSpread
    (rotation : Rotations.Basic.Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    1 + Matrix3.trace rotation.matrix =
      4 * (1 - Spread.halfSpread rotation) := by
  have fourNonzero := Characteristic.Nonzero.four_ne_zero twoNonzero
  have fourHalfSpread :
      4 * Spread.halfSpread rotation = 3 - Matrix3.trace rotation.matrix := by
    unfold Spread.halfSpread
    calc
      4 * ((3 - Matrix3.trace rotation.matrix) / 4) =
          ((3 - Matrix3.trace rotation.matrix) / 4) * 4 := by ring1
      _ = 3 - Matrix3.trace rotation.matrix :=
        Algebra.Field.ExplicitField.div_mul_cancel _ fourNonzero
  calc
    1 + Matrix3.trace rotation.matrix =
        4 * (1 - Spread.halfSpread rotation) +
          (4 * Spread.halfSpread rotation -
            (3 - Matrix3.trace rotation.matrix)) := by ring1
    _ = 4 * (1 - Spread.halfSpread rotation) := by
      rw [fourHalfSpread]
      ring1

/-- The recovered-anchor trace denominator is nonzero away from half spread one when two is nonzero. -/
theorem rotationAnchorDenominator_ne_zero (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    1 + Matrix3.trace rotation.matrix ≠ 0 := by
  have complementNonzero : 1 - Spread.halfSpread rotation ≠ 0 := by
    intro complementZero
    apply notHalfTurn
    calc
      Spread.halfSpread rotation = 1 - (1 - Spread.halfSpread rotation) := by ring1
      _ = 1 := by rw [complementZero]; ring1
  rw [Geometry.Rotations.Axis.Recovery.one_add_trace_eq_four_mul_one_sub_halfSpread rotation twoNonzero]
  exact Algebra.Field.ExplicitField.mul_ne_zero
    (Characteristic.Nonzero.four_ne_zero twoNonzero) complementNonzero

/-- For a rotation, `det(I+ρ)=2(1+tr ρ)`. -/
theorem determinant_identity_add_rotation (rotation : Rotations.Basic.Rotation K) :
    Matrix3.determinant
        (Matrix3.add Matrix3.identity rotation.matrix) =
      2 * (1 + Matrix3.trace rotation.matrix) := by
  have negatedSum :
      Matrix3.sub (Matrix3.scale (-1 : K) Matrix3.identity)
          rotation.matrix =
        Matrix3.neg (Matrix3.add Matrix3.identity rotation.matrix) := by
    ext <;> unfold Matrix3.sub Matrix3.scale Matrix3.identity Matrix3.neg
      Matrix3.add <;> ring1
  calc
    Matrix3.determinant
        (Matrix3.add Matrix3.identity rotation.matrix) =
      -Matrix3.determinant
        (Matrix3.neg
          (Matrix3.add Matrix3.identity rotation.matrix)) := by
            rw [Matrix3.determinant_neg]
            ring1
    _ = -Matrix3.characteristicValue rotation.matrix (-1) := by
      unfold Matrix3.characteristicValue
      rw [negatedSum]
    _ = 2 * (1 + Matrix3.trace rotation.matrix) := by
      rw [Matrix3.characteristicValue_expansion,
        Spread.principalTrace_rotation, rotation.determinantOne]
      ring1

/-- The matrix `I + R` has nonzero determinant away from half spread one when two is nonzero. -/
theorem determinant_identity_add_rotation_ne_zero (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.determinant
        (Matrix3.add Matrix3.identity rotation.matrix) ≠ 0 := by
  rw [Geometry.Rotations.Axis.Recovery.determinant_identity_add_rotation]
  exact Algebra.Field.ExplicitField.mul_ne_zero twoNonzero
    (Geometry.Rotations.Axis.Recovery.rotationAnchorDenominator_ne_zero rotation notHalfTurn twoNonzero)

/-- Definition 34's exact domain equivalence: the big Cayley denominator is invertible precisely away from half turns.
-/
theorem determinant_identity_add_rotation_ne_zero_iff
    (rotation : Rotations.Basic.Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.determinant
        (Matrix3.add Matrix3.identity rotation.matrix) ≠ 0 ↔
      Spread.halfSpread rotation ≠ 1 := by
  constructor
  · intro determinantNonzero halfTurnSpread
    apply determinantNonzero
    rw [Geometry.Rotations.Axis.Recovery.determinant_identity_add_rotation,
      Geometry.Rotations.Axis.Recovery.one_add_trace_eq_four_mul_one_sub_halfSpread rotation twoNonzero,
      halfTurnSpread]
    ring1
  · intro notHalfTurn
    exact Geometry.Rotations.Axis.Recovery.determinant_identity_add_rotation_ne_zero rotation notHalfTurn
      twoNonzero

/-- The left inverse relation missing from the stored row-orthogonality certificate. -/
theorem transpose_mul_rotation (rotation : Rotations.Basic.Rotation K) :
    Matrix3.mul (Matrix3.transpose rotation.matrix) rotation.matrix =
      Matrix3.identity := by
  calc
    Matrix3.mul (Matrix3.transpose rotation.matrix) rotation.matrix =
        Matrix3.mul (Matrix3.adjugate rotation.matrix) rotation.matrix := by
          rw [Spread.adjugate_rotation]
    _ = Matrix3.scale (Matrix3.determinant rotation.matrix)
        Matrix3.identity := Matrix3.adjugate_mul _
    _ = Matrix3.identity := by
      rw [rotation.determinantOne]
      ext <;> unfold Matrix3.scale Matrix3.identity <;> ring1

/-- Cayley--Hamilton reduction specialized to a rotation. -/
theorem rotation_square_sub_transpose (rotation : Rotations.Basic.Rotation K) :
    Matrix3.sub (Matrix3.mul rotation.matrix rotation.matrix)
        (Matrix3.transpose rotation.matrix) =
      Matrix3.scale (Matrix3.trace rotation.matrix)
        (Matrix3.sub rotation.matrix Matrix3.identity) := by
  rw [← Spread.adjugate_rotation rotation, Matrix3.adjugate_expansion,
    Spread.principalTrace_rotation]
  ext <;> unfold Matrix3.add Matrix3.sub Matrix3.scale Matrix3.identity <;>
    ring1

/-- Multiplying `R - Rᵀ` by `R + I` gives `(1 + tr R)(R - I)`. -/
private theorem anchorNumerator_mul_rotationSum (rotation : Rotations.Basic.Rotation K) :
    Matrix3.mul
        (Matrix3.sub rotation.matrix (Matrix3.transpose rotation.matrix))
        (Matrix3.add rotation.matrix Matrix3.identity) =
      Matrix3.scale (1 + Matrix3.trace rotation.matrix)
        (Matrix3.sub rotation.matrix Matrix3.identity) := by
  calc
    Matrix3.mul
        (Matrix3.sub rotation.matrix (Matrix3.transpose rotation.matrix))
        (Matrix3.add rotation.matrix Matrix3.identity) =
      Matrix3.sub
        (Matrix3.add (Matrix3.mul rotation.matrix rotation.matrix)
          rotation.matrix)
        (Matrix3.add Matrix3.identity
          (Matrix3.transpose rotation.matrix)) := by
            rw [Matrix3.mul_sub_left, Matrix3.mul_add_right,
              Matrix3.mul_add_right, Matrix3.mul_identity,
              Matrix3.mul_identity, Geometry.Rotations.Axis.Recovery.transpose_mul_rotation]
    _ = Matrix3.add
        (Matrix3.sub (Matrix3.mul rotation.matrix rotation.matrix)
          (Matrix3.transpose rotation.matrix))
        (Matrix3.sub rotation.matrix Matrix3.identity) := by
          ext <;> unfold Matrix3.add Matrix3.sub <;> ring1
    _ = Matrix3.add
        (Matrix3.scale (Matrix3.trace rotation.matrix)
          (Matrix3.sub rotation.matrix Matrix3.identity))
        (Matrix3.sub rotation.matrix Matrix3.identity) := by
          rw [Geometry.Rotations.Axis.Recovery.rotation_square_sub_transpose]
    _ = Matrix3.scale (1 + Matrix3.trace rotation.matrix)
        (Matrix3.sub rotation.matrix Matrix3.identity) := by
          ext <;> unfold Matrix3.add Matrix3.sub Matrix3.scale <;> ring1

/-- Multiplying `R + I` by `R - Rᵀ` gives `(1 + tr R)(R - I)`. -/
private theorem rotationSum_mul_anchorNumerator (rotation : Rotations.Basic.Rotation K) :
    Matrix3.mul
        (Matrix3.add rotation.matrix Matrix3.identity)
        (Matrix3.sub rotation.matrix (Matrix3.transpose rotation.matrix)) =
      Matrix3.scale (1 + Matrix3.trace rotation.matrix)
        (Matrix3.sub rotation.matrix Matrix3.identity) := by
  calc
    Matrix3.mul
        (Matrix3.add rotation.matrix Matrix3.identity)
        (Matrix3.sub rotation.matrix (Matrix3.transpose rotation.matrix)) =
      Matrix3.sub
        (Matrix3.add (Matrix3.mul rotation.matrix rotation.matrix)
          rotation.matrix)
        (Matrix3.add Matrix3.identity
          (Matrix3.transpose rotation.matrix)) := by
            rw [Matrix3.mul_sub_right, Matrix3.mul_add_left,
              Matrix3.mul_add_left, Matrix3.identity_mul,
              Matrix3.identity_mul, rotation.orthogonal]
    _ = Matrix3.add
        (Matrix3.sub (Matrix3.mul rotation.matrix rotation.matrix)
          (Matrix3.transpose rotation.matrix))
        (Matrix3.sub rotation.matrix Matrix3.identity) := by
          ext <;> unfold Matrix3.add Matrix3.sub <;> ring1
    _ = Matrix3.add
        (Matrix3.scale (Matrix3.trace rotation.matrix)
          (Matrix3.sub rotation.matrix Matrix3.identity))
        (Matrix3.sub rotation.matrix Matrix3.identity) := by
          rw [Geometry.Rotations.Axis.Recovery.rotation_square_sub_transpose]
    _ = Matrix3.scale (1 + Matrix3.trace rotation.matrix)
        (Matrix3.sub rotation.matrix Matrix3.identity) := by
          ext <;> unfold Matrix3.add Matrix3.sub Matrix3.scale <;> ring1

/-- The recovered anchor times `R + I` equals `R - I`. -/
theorem rotationAnchor_mul_rotationSum (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.mul (Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn)
        (Matrix3.add rotation.matrix Matrix3.identity) =
      Matrix3.sub rotation.matrix Matrix3.identity := by
  have denominatorNonzero := Geometry.Rotations.Axis.Recovery.rotationAnchorDenominator_ne_zero rotation
    notHalfTurn twoNonzero
  have coefficient :
      (1 / (1 + Matrix3.trace rotation.matrix)) *
        (1 + Matrix3.trace rotation.matrix) = (1 : K) := by
    exact Algebra.Field.ExplicitField.div_mul_cancel 1 denominatorNonzero
  unfold Geometry.Rotations.Axis.Recovery.rotationAnchor
  rw [Matrix3.mul_scale_left, Geometry.Rotations.Axis.Recovery.anchorNumerator_mul_rotationSum,
    Matrix3.scale_scale, coefficient]
  ext <;> unfold Matrix3.scale <;> ring1

/-- The product of `R + I` with the recovered anchor equals `R - I`. -/
theorem rotationSum_mul_rotationAnchor (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.mul (Matrix3.add rotation.matrix Matrix3.identity)
        (Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn) =
      Matrix3.sub rotation.matrix Matrix3.identity := by
  have denominatorNonzero := Geometry.Rotations.Axis.Recovery.rotationAnchorDenominator_ne_zero rotation
    notHalfTurn twoNonzero
  have coefficient :
      (1 / (1 + Matrix3.trace rotation.matrix)) *
        (1 + Matrix3.trace rotation.matrix) = (1 : K) :=
    Algebra.Field.ExplicitField.div_mul_cancel 1 denominatorNonzero
  unfold Geometry.Rotations.Axis.Recovery.rotationAnchor
  rw [Matrix3.mul_scale_right, Geometry.Rotations.Axis.Recovery.rotationSum_mul_anchorNumerator,
    Matrix3.scale_scale, coefficient]
  ext <;> unfold Matrix3.scale <;> ring1

/-- The recovered rotation anchor equals its inverse Cayley expression.

For a rotation that is not a half turn and nonzero two, the cached anchor is `(R-I)(I+R)⁻¹`; the inverse carries the
proved nonzero determinant of `I+R` (Definition 34). -/
theorem rotationAnchor_eq_bigCayleyFormula (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn =
      Matrix3.mul (Matrix3.sub rotation.matrix Matrix3.identity)
        (Matrix3.inverse
          (Matrix3.add Matrix3.identity rotation.matrix)
          (Geometry.Rotations.Axis.Recovery.determinant_identity_add_rotation_ne_zero rotation notHalfTurn
            twoNonzero)) := by
  let sum := Matrix3.add Matrix3.identity rotation.matrix
  let sumInverse := Matrix3.inverse sum
    (Geometry.Rotations.Axis.Recovery.determinant_identity_add_rotation_ne_zero rotation notHalfTurn
      twoNonzero)
  have rightInverse : Matrix3.mul sum sumInverse = Matrix3.identity :=
    Matrix3.mul_inverse sum _
  calc
    Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn =
        Matrix3.mul (Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn) Matrix3.identity := by
          rw [Matrix3.mul_identity]
    _ = Matrix3.mul (Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn)
        (Matrix3.mul sum sumInverse) := by rw [rightInverse]
    _ = Matrix3.mul
        (Matrix3.mul (Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn) sum) sumInverse := by
          rw [Matrix3.mul_assoc]
    _ = Matrix3.mul (Matrix3.sub rotation.matrix Matrix3.identity)
        sumInverse := by
          unfold sum
          rw [show Matrix3.add Matrix3.identity rotation.matrix =
              Matrix3.add rotation.matrix Matrix3.identity by
                ext <;> unfold Matrix3.add <;> ring1,
            Geometry.Rotations.Axis.Recovery.rotationAnchor_mul_rotationSum rotation notHalfTurn twoNonzero]
    _ = Matrix3.mul (Matrix3.sub rotation.matrix Matrix3.identity)
        (Matrix3.inverse
          (Matrix3.add Matrix3.identity rotation.matrix)
          (Geometry.Rotations.Axis.Recovery.determinant_identity_add_rotation_ne_zero rotation notHalfTurn
            twoNonzero)) := by
          rfl

/-- The anchor is the negative big Cayley transform. -/
theorem rotationAnchor_eq_neg_bigCayley (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn =
      Matrix3.neg
        (Coordinates3.Cayley.bigCayley rotation.matrix
          (Geometry.Rotations.Axis.Recovery.determinant_identity_add_rotation_ne_zero rotation notHalfTurn
            twoNonzero)) := by
  rw [Geometry.Rotations.Axis.Recovery.rotationAnchor_eq_bigCayleyFormula rotation notHalfTurn twoNonzero]
  unfold Coordinates3.Cayley.bigCayley
  ext <;> unfold Matrix3.mul Matrix3.sub Matrix3.neg <;> ring1

/-- Theorem 35.1: the recovered anchor is antisymmetric. -/
theorem rotationAnchor_isAntisymmetric (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1) :
    Matrix3.IsAntisymmetric (Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn) := by
  unfold Matrix3.IsAntisymmetric Geometry.Rotations.Axis.Recovery.rotationAnchor
  rw [Matrix3.transpose_scale, Matrix3.transpose_sub,
    Matrix3.transpose_transpose]
  ext <;> unfold Matrix3.transpose Matrix3.sub Matrix3.neg Matrix3.scale <;>
    ring1

/-- The recovered vector re-encodes the recovered anchor. -/
theorem anchor_rotationAnchorVector (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Antisymmetric.anchor (Geometry.Rotations.Axis.Recovery.rotationAnchorVector rotation notHalfTurn) =
      Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn := by
  exact Antisymmetric.anchor_anchorVector_of_isAntisymmetric _ twoNonzero
    (Geometry.Rotations.Axis.Recovery.rotationAnchor_isAntisymmetric rotation notHalfTurn)

/-- Theorem 35.1: uniqueness of the recovered anchor vector. -/
theorem rotationAnchorVector_unique (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) (vector : Coordinates3.Vector K)
    (encodes : Antisymmetric.anchor vector = Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn) :
    vector = Geometry.Rotations.Axis.Recovery.rotationAnchorVector rotation notHalfTurn := by
  apply Antisymmetric.anchor_injective
  rw [encodes, Geometry.Rotations.Axis.Recovery.anchor_rotationAnchorVector rotation notHalfTurn twoNonzero]

/-- Express the recovered rotation anchor as a scaled antisymmetric part.

For a rotation that is not a half turn and nonzero two, scale the antisymmetric part of `R` by `2 / (1 + trace R)` to
recover its anchor (Theorem 35.5). -/
theorem rotationAnchor_eq_antisymmetricPart (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn =
      Matrix3.scale (2 / (1 + Matrix3.trace rotation.matrix))
        (Antisymmetric.antisymmetricPart rotation.matrix) := by
  have twoCancel := Algebra.Field.ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  unfold Geometry.Rotations.Axis.Recovery.rotationAnchor Antisymmetric.antisymmetricPart
  rw [Matrix3.scale_scale]
  have coefficient :
      (2 / (1 + Matrix3.trace rotation.matrix)) * (1 / 2) =
        1 / (1 + Matrix3.trace rotation.matrix) := by
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      2 * (1 + Matrix3.trace rotation.matrix)⁻¹ *
          (1 * (2 : K)⁻¹) =
        (1 + Matrix3.trace rotation.matrix)⁻¹ *
          (2 * (2 : K)⁻¹) := by ring1
      _ = 1 * (1 + Matrix3.trace rotation.matrix)⁻¹ := by
        rw [twoCancel]
        ring1
  rw [coefficient]

/-- The cached anchor of a cap is the original anchor. -/
theorem rotationAnchor_cap (vector : Coordinates3.Vector K)
    (defined : Cap.capDenominator vector ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    Geometry.Rotations.Axis.Recovery.rotationAnchor (Cap.capRotation vector defined)
        (Spread.halfSpread_cap_ne_one vector defined twoNonzero) =
      Antisymmetric.anchor vector := by
  have traceDenominator :
      1 + Matrix3.trace (Cap.cap vector defined) =
        4 / Cap.capDenominator vector := by
    have cancel := Algebra.Field.ExplicitField.mul_inv_cancel
      (Cap.capDenominator vector) defined
    rw [Cap.trace_cap]
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      1 + (3 - vector.quadrance) * (Cap.capDenominator vector)⁻¹ =
          Cap.capDenominator vector * (Cap.capDenominator vector)⁻¹ +
            (3 - vector.quadrance) *
              (Cap.capDenominator vector)⁻¹ := by rw [cancel]
      _ = 4 * (Cap.capDenominator vector)⁻¹ := by
        unfold Cap.capDenominator
        ring1
  have scalarNonzero : 4 / Cap.capDenominator vector ≠ 0 :=
    Algebra.Field.ExplicitField.div_ne_zero (Characteristic.Nonzero.four_ne_zero twoNonzero) defined
  unfold Geometry.Rotations.Axis.Recovery.rotationAnchor Cap.capRotation
  rw [traceDenominator, Cap.cap_antisymmetric_part, Matrix3.scale_scale]
  have coefficient :
      (1 / (4 / Cap.capDenominator vector)) *
        (4 / Cap.capDenominator vector) = (1 : K) :=
    Algebra.Field.ExplicitField.div_mul_cancel 1 scalarNonzero
  rw [coefficient]
  ext <;> unfold Matrix3.scale <;> ring1

/-- The recovered anchor satisfies the Cayley relation with its rotation. -/
theorem identity_sub_rotationAnchor_mul_rotation (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.mul
        (Matrix3.sub Matrix3.identity
          (Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn))
        rotation.matrix =
      Matrix3.add Matrix3.identity
        (Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn) := by
  have expanded := Geometry.Rotations.Axis.Recovery.rotationAnchor_mul_rotationSum rotation notHalfTurn
    twoNonzero
  rw [Matrix3.mul_add_right, Matrix3.mul_identity] at expanded
  have anchorTimesRotation :
      Matrix3.mul (Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn) rotation.matrix =
        Matrix3.sub (Matrix3.sub rotation.matrix Matrix3.identity)
          (Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn) :=
    Matrix3.eq_sub_of_add_eq expanded
  calc
    Matrix3.mul
        (Matrix3.sub Matrix3.identity
          (Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn))
        rotation.matrix =
      Matrix3.sub rotation.matrix
        (Matrix3.mul (Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn)
          rotation.matrix) := by
            rw [Matrix3.mul_sub_left, Matrix3.identity_mul]
    _ = Matrix3.sub rotation.matrix
        (Matrix3.sub (Matrix3.sub rotation.matrix Matrix3.identity)
          (Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn)) := by
            rw [anchorTimesRotation]
    _ = Matrix3.add Matrix3.identity
        (Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn) := by
          ext <;> unfold Matrix3.add Matrix3.sub <;> ring1

/-- The product of `I - A` with `R + I` is twice the identity for the recovered anchor. -/
private theorem identity_sub_rotationAnchor_mul_rotationSum
    (rotation : Rotations.Basic.Rotation K) (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.mul
        (Matrix3.sub Matrix3.identity
          (Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn))
        (Matrix3.add rotation.matrix Matrix3.identity) =
      Matrix3.scale 2 Matrix3.identity := by
  calc
    Matrix3.mul
        (Matrix3.sub Matrix3.identity
          (Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn))
        (Matrix3.add rotation.matrix Matrix3.identity) =
      Matrix3.sub (Matrix3.add rotation.matrix Matrix3.identity)
        (Matrix3.mul (Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn)
          (Matrix3.add rotation.matrix Matrix3.identity)) := by
            rw [Matrix3.mul_sub_left, Matrix3.identity_mul]
    _ = Matrix3.sub (Matrix3.add rotation.matrix Matrix3.identity)
        (Matrix3.sub rotation.matrix Matrix3.identity) := by
          rw [Geometry.Rotations.Axis.Recovery.rotationAnchor_mul_rotationSum rotation notHalfTurn twoNonzero]
    _ = Matrix3.scale 2 Matrix3.identity := by
      ext <;> unfold Matrix3.add Matrix3.sub Matrix3.scale Matrix3.identity <;>
        ring1

/-- Half of `R + I` is a right inverse for identity minus the recovered anchor. -/
private theorem identity_sub_rotationAnchor_has_rightInverse
    (rotation : Rotations.Basic.Rotation K) (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.mul
        (Matrix3.sub Matrix3.identity
          (Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn))
        (Matrix3.scale (1 / 2)
          (Matrix3.add rotation.matrix Matrix3.identity)) =
      Matrix3.identity := by
  have coefficient : (1 / 2 : K) * 2 = 1 :=
    Algebra.Field.ExplicitField.div_mul_cancel 1 twoNonzero
  rw [Matrix3.mul_scale_right,
    Geometry.Rotations.Axis.Recovery.identity_sub_rotationAnchor_mul_rotationSum rotation notHalfTurn
      twoNonzero,
    Matrix3.scale_scale, coefficient]
  ext <;> unfold Matrix3.scale Matrix3.identity <;> ring1

/-- The anchor vector recovered from a non-half-turn rotation lies in the cap domain. -/
theorem rotationAnchorVector_capDefined (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Cap.capDenominator (Geometry.Rotations.Axis.Recovery.rotationAnchorVector rotation notHalfTurn) ≠ 0 := by
  let anchorMatrix := Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn
  let rightInverse := Matrix3.scale (1 / 2)
    (Matrix3.add rotation.matrix Matrix3.identity)
  have inverseCertificate :
      Matrix3.mul (Matrix3.sub Matrix3.identity anchorMatrix) rightInverse =
        Matrix3.identity := by
    unfold anchorMatrix rightInverse
    exact Geometry.Rotations.Axis.Recovery.identity_sub_rotationAnchor_has_rightInverse rotation
      notHalfTurn
      twoNonzero
  have determinantProduct := congrArg Matrix3.determinant inverseCertificate
  rw [Matrix3.determinant_mul, Matrix3.determinant_identity]
    at determinantProduct
  have determinantNonzero :
      Matrix3.determinant
        (Matrix3.sub Matrix3.identity anchorMatrix) ≠ 0 := by
    intro determinantZero
    rw [determinantZero, zero_mul] at determinantProduct
    exact (Purelib.Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero twoNonzero) determinantProduct.symm
  rw [← Cap.determinant_identity_sub_anchor]
  have encodes := Geometry.Rotations.Axis.Recovery.anchor_rotationAnchorVector rotation notHalfTurn twoNonzero
  rw [encodes]
  exact determinantNonzero

/-- Theorem 35.2: taking the cap of the recovered anchor returns the original rotation matrix. -/
theorem cap_rotationAnchor (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Cap.cap (Geometry.Rotations.Axis.Recovery.rotationAnchorVector rotation notHalfTurn)
        (Geometry.Rotations.Axis.Recovery.rotationAnchorVector_capDefined rotation notHalfTurn twoNonzero) =
      rotation.matrix := by
  let vector := Geometry.Rotations.Axis.Recovery.rotationAnchorVector rotation notHalfTurn
  let capDefined := Geometry.Rotations.Axis.Recovery.rotationAnchorVector_capDefined rotation notHalfTurn
    twoNonzero
  have encodes : Antisymmetric.anchor vector = Geometry.Rotations.Axis.Recovery.rotationAnchor rotation notHalfTurn :=
    by
    unfold vector
    exact Geometry.Rotations.Axis.Recovery.anchor_rotationAnchorVector rotation notHalfTurn twoNonzero
  have rotationRelation := Geometry.Rotations.Axis.Recovery.identity_sub_rotationAnchor_mul_rotation rotation
    notHalfTurn twoNonzero
  rw [← encodes] at rotationRelation
  have capRelation := Cap.identity_sub_anchor_mul_cap vector capDefined
  have inverseLeft := Cap.anchorResolventInverse_right vector capDefined
  calc
    Cap.cap vector capDefined =
        Matrix3.mul Matrix3.identity (Cap.cap vector capDefined) := by
          rw [Matrix3.identity_mul]
    _ = Matrix3.mul
        (Matrix3.mul (Cap.anchorResolventInverse vector capDefined)
          (Matrix3.sub Matrix3.identity (Antisymmetric.anchor vector)))
        (Cap.cap vector capDefined) := by rw [inverseLeft]
    _ = Matrix3.mul (Cap.anchorResolventInverse vector capDefined)
        (Matrix3.mul (Matrix3.sub Matrix3.identity (Antisymmetric.anchor vector))
          (Cap.cap vector capDefined)) := by rw [Matrix3.mul_assoc]
    _ = Matrix3.mul (Cap.anchorResolventInverse vector capDefined)
        (Matrix3.add Matrix3.identity (Antisymmetric.anchor vector)) := by
          rw [capRelation]
    _ = Matrix3.mul (Cap.anchorResolventInverse vector capDefined)
        (Matrix3.mul (Matrix3.sub Matrix3.identity (Antisymmetric.anchor vector))
          rotation.matrix) := by rw [rotationRelation]
    _ = Matrix3.mul
        (Matrix3.mul (Cap.anchorResolventInverse vector capDefined)
          (Matrix3.sub Matrix3.identity (Antisymmetric.anchor vector)))
        rotation.matrix := by rw [Matrix3.mul_assoc]
    _ = rotation.matrix := by rw [inverseLeft, Matrix3.identity_mul]

/-- Theorem 35.3: a rotation fixes its recovered anchor vector. -/
theorem rowMul_rotationAnchorVector (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.rowMul (Geometry.Rotations.Axis.Recovery.rotationAnchorVector rotation notHalfTurn)
        rotation.matrix =
      Geometry.Rotations.Axis.Recovery.rotationAnchorVector rotation notHalfTurn := by
  rw [← Geometry.Rotations.Axis.Recovery.cap_rotationAnchor rotation notHalfTurn twoNonzero]
  exact Cap.rowMul_self_cap _ _

/-- The half spread is unchanged when the rotation is replaced by the cap of its recovered anchor. -/
private theorem halfSpread_recoveredCap (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Spread.halfSpread
        (Cap.capRotation (Geometry.Rotations.Axis.Recovery.rotationAnchorVector rotation notHalfTurn)
          (Geometry.Rotations.Axis.Recovery.rotationAnchorVector_capDefined rotation notHalfTurn twoNonzero)) =
      Spread.halfSpread rotation := by
  have traceEqual := congrArg Matrix3.trace
    (Geometry.Rotations.Axis.Recovery.cap_rotationAnchor rotation notHalfTurn twoNonzero)
  unfold Spread.halfSpread Cap.capRotation
  rw [traceEqual]

/-- Theorem 35.4: quadrance of the recovered anchor vector. -/
theorem quadrance_rotationAnchorVector (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    (Geometry.Rotations.Axis.Recovery.rotationAnchorVector rotation notHalfTurn).quadrance =
      Spread.halfSpread rotation / (1 - Spread.halfSpread rotation) := by
  let vector := Geometry.Rotations.Axis.Recovery.rotationAnchorVector rotation notHalfTurn
  let defined := Geometry.Rotations.Axis.Recovery.rotationAnchorVector_capDefined rotation notHalfTurn
    twoNonzero
  have recovered := Spread.quadrance_eq_halfSpread_div_one_sub vector defined
    twoNonzero
  rw [Geometry.Rotations.Axis.Recovery.halfSpread_recoveredCap rotation notHalfTurn
    twoNonzero] at recovered
  exact recovered

/-- The vector in the anchor formula for a product of two reflections. -/
@[expose] public def reflectionProductAnchorVector (first second : Coordinates3.Vector K)
    (_dotNonzero : Coordinates3.Vector.dot first second ≠ 0) : Coordinates3.Vector K :=
  Coordinates3.Vector.scale (1 / Coordinates3.Vector.dot first second) (Coordinates3.Vector.cross first second)

/-- Non-perpendicular mirror normals give a non-half-turn product. -/
theorem reflectionProduct_notHalfTurn (first second : Coordinates3.Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0)
    (dotNonzero : Coordinates3.Vector.dot first second ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    Spread.halfSpread
        (Reflection.reflectionProductRotation first second firstNonNull secondNonNull) ≠
      1 := by
  have denominatorNonzero : first.quadrance * second.quadrance ≠ 0 :=
    Algebra.Field.ExplicitField.mul_ne_zero firstNonNull secondNonNull
  have dotSquareNonzero : Coordinates3.Vector.dot first second ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      Algebra.Field.ExplicitField.mul_ne_zero dotNonzero dotNonzero
  have quotientNonzero :
      Coordinates3.Vector.dot first second ^ 2 /
        (first.quadrance * second.quadrance) ≠ 0 :=
    Algebra.Field.ExplicitField.div_ne_zero dotSquareNonzero denominatorNonzero
  rw [Spread.halfSpread_reflectionProduct first second firstNonNull secondNonNull
    twoNonzero]
  intro spreadOne
  apply quotientNonzero
  unfold Coordinates3.Vector.spread at spreadOne
  calc
    Coordinates3.Vector.dot first second ^ 2 /
        (first.quadrance * second.quadrance) =
      1 - (1 - Coordinates3.Vector.dot first second ^ 2 /
        (first.quadrance * second.quadrance)) := by ring1
    _ = 0 := by rw [spreadOne]; ring1

/-- The antisymmetric part of a two-reflection product is the cross-product anchor scaled by the normals' dot product
and quadrances. -/
private theorem reflectionProduct_antisymmetricNumerator
    (first second : Coordinates3.Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0) :
    Matrix3.sub
        (Matrix3.mul (Reflection.reflection first firstNonNull)
          (Reflection.reflection second secondNonNull))
        (Matrix3.transpose
          (Matrix3.mul (Reflection.reflection first firstNonNull)
            (Reflection.reflection second secondNonNull))) =
      Matrix3.scale
        (4 * Coordinates3.Vector.dot first second /
          (first.quadrance * second.quadrance))
        (Antisymmetric.anchor (Coordinates3.Vector.cross first second)) := by
  have productInverse := Purelib.Algebra.Field.Inverse.inverse_product firstNonNull
    secondNonNull
  rw [Matrix3.transpose_mul, Reflection.reflection_transpose, Reflection.reflection_transpose]
  ext <;> unfold Reflection.reflection Matrix3.mul Matrix3.sub Matrix3.identity
    Matrix3.scale Matrix3.outer Antisymmetric.anchor Coordinates3.Vector.cross <;>
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv, productInverse] <;>
    unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot <;> ring1

/-- One plus the two-reflection trace is four times the squared normal dot product divided by their quadrance product.
-/
private theorem one_add_trace_reflectionProduct
    (first second : Coordinates3.Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0) :
    1 + Matrix3.trace
        (Matrix3.mul (Reflection.reflection first firstNonNull)
          (Reflection.reflection second secondNonNull)) =
      4 * Coordinates3.Vector.dot first second ^ 2 /
        (first.quadrance * second.quadrance) := by
  rw [Spread.trace_reflection_product]
  unfold Coordinates3.Vector.spread
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  ring1

/-- Theorem 37: anchor of a product of two non-perpendicular reflections. -/
theorem rotationAnchor_reflectionProduct (first second : Coordinates3.Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0)
    (dotNonzero : Coordinates3.Vector.dot first second ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    Geometry.Rotations.Axis.Recovery.rotationAnchor
        (Reflection.reflectionProductRotation first second firstNonNull secondNonNull)
        (Geometry.Rotations.Axis.Recovery.reflectionProduct_notHalfTurn first second firstNonNull secondNonNull
          dotNonzero twoNonzero) =
      Antisymmetric.anchor (Geometry.Rotations.Axis.Recovery.reflectionProductAnchorVector first second dotNonzero) :=
        by
  let quadranceProduct := first.quadrance * second.quadrance
  let traceDenominator :=
    4 * Coordinates3.Vector.dot first second ^ 2 / quadranceProduct
  let numeratorScalar :=
    4 * Coordinates3.Vector.dot first second / quadranceProduct
  have quadranceProductNonzero : quadranceProduct ≠ 0 :=
    Algebra.Field.ExplicitField.mul_ne_zero firstNonNull secondNonNull
  have fourNonzero := Characteristic.Nonzero.four_ne_zero twoNonzero
  have dotSquareNonzero : Coordinates3.Vector.dot first second ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      Algebra.Field.ExplicitField.mul_ne_zero dotNonzero dotNonzero
  have traceDenominatorNonzero : traceDenominator ≠ 0 := by
    unfold traceDenominator
    exact Algebra.Field.ExplicitField.div_ne_zero
      (Algebra.Field.ExplicitField.mul_ne_zero fourNonzero dotSquareNonzero)
      quadranceProductNonzero
  have coefficient :
      (1 / traceDenominator) * numeratorScalar =
        1 / Coordinates3.Vector.dot first second := by
    calc
      (1 / traceDenominator) * numeratorScalar =
          numeratorScalar / traceDenominator := by
            simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
            ring1
      _ = 1 / Coordinates3.Vector.dot first second := by
        apply Purelib.Algebra.Field.Inverse.div_eq_div_of_cross_mul traceDenominatorNonzero
          dotNonzero
        unfold numeratorScalar traceDenominator quadranceProduct
        simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
        ring1
  unfold Geometry.Rotations.Axis.Recovery.rotationAnchor Reflection.reflectionProductRotation
  rw [Geometry.Rotations.Axis.Recovery.one_add_trace_reflectionProduct,
    Geometry.Rotations.Axis.Recovery.reflectionProduct_antisymmetricNumerator, Matrix3.scale_scale]
  change Matrix3.scale ((1 / traceDenominator) * numeratorScalar)
      (Antisymmetric.anchor (Coordinates3.Vector.cross first second)) =
    Antisymmetric.anchor (Geometry.Rotations.Axis.Recovery.reflectionProductAnchorVector first second dotNonzero)
  rw [coefficient]
  exact (Antisymmetric.anchor_scale _ _).symm

/-- Express the anchor of two reflections by their skew outer-product difference.

For non-null normals with nonzero dot product and nonzero two, divide the difference of their two ordered outer products
by that dot product (Theorem 37). -/
theorem rotationAnchor_reflectionProduct_outerFormula
    (first second : Coordinates3.Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0)
    (dotNonzero : Coordinates3.Vector.dot first second ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    Geometry.Rotations.Axis.Recovery.rotationAnchor
        (Reflection.reflectionProductRotation first second firstNonNull secondNonNull)
        (Geometry.Rotations.Axis.Recovery.reflectionProduct_notHalfTurn first second firstNonNull secondNonNull
          dotNonzero twoNonzero) =
      Matrix3.scale (1 / Coordinates3.Vector.dot first second)
        (Matrix3.sub (Matrix3.outer first second)
          (Matrix3.outer second first)) := by
  rw [Geometry.Rotations.Axis.Recovery.rotationAnchor_reflectionProduct first second firstNonNull secondNonNull
      dotNonzero twoNonzero,
    Antisymmetric.outer_commutator_eq_anchor_cross]
  exact Antisymmetric.anchor_scale _ _

/-- The vector recovered by the general anchor construction is the explicit cross-product formula of Theorem 37. -/
theorem rotationAnchorVector_reflectionProduct (first second : Coordinates3.Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0)
    (dotNonzero : Coordinates3.Vector.dot first second ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    Geometry.Rotations.Axis.Recovery.rotationAnchorVector
        (Reflection.reflectionProductRotation first second firstNonNull secondNonNull)
        (Geometry.Rotations.Axis.Recovery.reflectionProduct_notHalfTurn first second firstNonNull secondNonNull
          dotNonzero twoNonzero) =
      Geometry.Rotations.Axis.Recovery.reflectionProductAnchorVector first second dotNonzero := by
  apply Antisymmetric.anchor_injective
  rw [Geometry.Rotations.Axis.Recovery.anchor_rotationAnchorVector _ _ twoNonzero,
    Geometry.Rotations.Axis.Recovery.rotationAnchor_reflectionProduct first second firstNonNull secondNonNull
      dotNonzero twoNonzero]

/-- Theorem 38: quadrance of the two-reflection anchor vector. -/
theorem quadrance_reflectionProductAnchorVector (first second : Coordinates3.Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0)
    (dotNonzero : Coordinates3.Vector.dot first second ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    (Geometry.Rotations.Axis.Recovery.reflectionProductAnchorVector first second dotNonzero).quadrance =
      Coordinates3.Vector.spread first second firstNonNull secondNonNull /
        (1 - Coordinates3.Vector.spread first second firstNonNull secondNonNull) := by
  have recovered := Geometry.Rotations.Axis.Recovery.quadrance_rotationAnchorVector
    (Reflection.reflectionProductRotation first second firstNonNull secondNonNull)
    (Geometry.Rotations.Axis.Recovery.reflectionProduct_notHalfTurn first second firstNonNull secondNonNull
      dotNonzero twoNonzero) twoNonzero
  rw [Geometry.Rotations.Axis.Recovery.rotationAnchorVector_reflectionProduct first second firstNonNull
      secondNonNull dotNonzero twoNonzero,
    Spread.halfSpread_reflectionProduct first second firstNonNull secondNonNull
      twoNonzero] at recovered
  exact recovered

/-- Theorem 38's independent rescaling of the two mirror lines. -/
theorem reflectionProductAnchorVector_scale (first second : Coordinates3.Vector K)
    (firstScalar secondScalar : K)
    (firstScalarNonzero : firstScalar ≠ 0)
    (secondScalarNonzero : secondScalar ≠ 0)
    (dotNonzero : Coordinates3.Vector.dot first second ≠ 0) :
    Geometry.Rotations.Axis.Recovery.reflectionProductAnchorVector
        (Coordinates3.Vector.scale firstScalar first)
        (Coordinates3.Vector.scale secondScalar second)
        (by
          rw [Coordinates3.Vector.dot_scale_left, Coordinates3.Vector.dot_scale_right]
          exact Algebra.Field.ExplicitField.mul_ne_zero
            firstScalarNonzero
            (Algebra.Field.ExplicitField.mul_ne_zero secondScalarNonzero
              dotNonzero)) =
      Geometry.Rotations.Axis.Recovery.reflectionProductAnchorVector first second dotNonzero := by
  let factor := firstScalar * secondScalar
  have factorNonzero : factor ≠ 0 :=
    Algebra.Field.ExplicitField.mul_ne_zero firstScalarNonzero secondScalarNonzero
  have factorCancel := Algebra.Field.ExplicitField.mul_inv_cancel factor factorNonzero
  have productInverse := Purelib.Algebra.Field.Inverse.inverse_product factorNonzero
    dotNonzero
  have coefficient :
      (1 / (factor * Coordinates3.Vector.dot first second)) * factor =
        1 / Coordinates3.Vector.dot first second := by
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv, productInverse]
    calc
      1 * (factor⁻¹ * (Coordinates3.Vector.dot first second)⁻¹) * factor =
          (Coordinates3.Vector.dot first second)⁻¹ * (factor * factor⁻¹) := by
            ring1
      _ = 1 * (Coordinates3.Vector.dot first second)⁻¹ := by
        rw [factorCancel, mul_one, one_mul]
  unfold Geometry.Rotations.Axis.Recovery.reflectionProductAnchorVector
  rw [Coordinates3.Vector.dot_scale_left, Coordinates3.Vector.dot_scale_right,
    Coordinates3.Vector.cross_scale_left, Coordinates3.Vector.cross_scale_right,
    Coordinates3.Vector.scale_scale, Coordinates3.Vector.scale_scale]
  have denominator :
      firstScalar * (secondScalar * Coordinates3.Vector.dot first second) =
        factor * Coordinates3.Vector.dot first second := by
    unfold factor
    ring1
  rw [denominator]
  have scaledCoefficient :
      1 / (factor * Coordinates3.Vector.dot first second) * firstScalar * secondScalar =
        (1 / (factor * Coordinates3.Vector.dot first second)) * factor := by
    unfold factor
    ring1
  rw [scaledCoefficient, coefficient]

/-! ### The missing half-turn classification used by Theorem 40 -/

/-- Half spread one forces the rotation trace to be minus one when two is nonzero. -/
private theorem trace_eq_neg_one_of_halfSpread_eq_one
    (rotation : Rotations.Basic.Rotation K) (halfTurnSpread : Spread.halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.trace rotation.matrix = -1 := by
  have traceRelation :=
    Geometry.Rotations.Axis.Recovery.one_add_trace_eq_four_mul_one_sub_halfSpread rotation twoNonzero
  rw [halfTurnSpread] at traceRelation
  calc
    Matrix3.trace rotation.matrix =
        (1 + Matrix3.trace rotation.matrix) - 1 := by ring1
    _ = -1 := by rw [traceRelation]; ring1

/-- The transposed rotation satisfies the corresponding Cayley–Hamilton quadratic identity. -/
private theorem transpose_square_sub_rotation (rotation : Rotations.Basic.Rotation K) :
    Matrix3.sub
        (Matrix3.mul (Matrix3.transpose rotation.matrix)
          (Matrix3.transpose rotation.matrix))
        rotation.matrix =
      Matrix3.scale (Matrix3.trace rotation.matrix)
        (Matrix3.sub (Matrix3.transpose rotation.matrix)
          Matrix3.identity) := by
  have transposed := congrArg Matrix3.transpose
    (Geometry.Rotations.Axis.Recovery.rotation_square_sub_transpose rotation)
  simpa only [Matrix3.transpose_sub, Matrix3.transpose_mul,
    Matrix3.transpose_transpose, Matrix3.transpose_scale,
    Matrix3.transpose_identity, Coordinates3.Matrix3.trace_transpose] using transposed

/-- The square of `R - Rᵀ` equals `(1 + tr R)(R + Rᵀ - 2I)`. -/
private theorem rotationAntisymmetricNumerator_square
    (rotation : Rotations.Basic.Rotation K) :
    Matrix3.mul
        (Matrix3.sub rotation.matrix
          (Matrix3.transpose rotation.matrix))
        (Matrix3.sub rotation.matrix
          (Matrix3.transpose rotation.matrix)) =
      Matrix3.scale (1 + Matrix3.trace rotation.matrix)
        (Matrix3.sub
          (Matrix3.add rotation.matrix
            (Matrix3.transpose rotation.matrix))
          (Matrix3.scale 2 Matrix3.identity)) := by
  calc
    Matrix3.mul
        (Matrix3.sub rotation.matrix
          (Matrix3.transpose rotation.matrix))
        (Matrix3.sub rotation.matrix
          (Matrix3.transpose rotation.matrix)) =
      Matrix3.sub
        (Matrix3.sub
          (Matrix3.mul rotation.matrix rotation.matrix)
          Matrix3.identity)
        (Matrix3.sub Matrix3.identity
          (Matrix3.mul (Matrix3.transpose rotation.matrix)
            (Matrix3.transpose rotation.matrix))) := by
              rw [Matrix3.mul_sub_right, Matrix3.mul_sub_left,
                Matrix3.mul_sub_left, rotation.orthogonal,
                Geometry.Rotations.Axis.Recovery.transpose_mul_rotation]
    _ = Matrix3.add
        (Matrix3.add
          (Matrix3.sub
            (Matrix3.mul rotation.matrix rotation.matrix)
            (Matrix3.transpose rotation.matrix))
          (Matrix3.sub
            (Matrix3.mul (Matrix3.transpose rotation.matrix)
              (Matrix3.transpose rotation.matrix))
            rotation.matrix))
        (Matrix3.sub
          (Matrix3.add rotation.matrix
            (Matrix3.transpose rotation.matrix))
          (Matrix3.scale 2 Matrix3.identity)) := by
            ext <;> unfold Matrix3.add Matrix3.sub Matrix3.scale
              Matrix3.identity <;> ring1
    _ = Matrix3.add
        (Matrix3.add
          (Matrix3.scale (Matrix3.trace rotation.matrix)
            (Matrix3.sub rotation.matrix Matrix3.identity))
          (Matrix3.scale (Matrix3.trace rotation.matrix)
            (Matrix3.sub (Matrix3.transpose rotation.matrix)
              Matrix3.identity)))
        (Matrix3.sub
          (Matrix3.add rotation.matrix
            (Matrix3.transpose rotation.matrix))
          (Matrix3.scale 2 Matrix3.identity)) := by
            rw [Geometry.Rotations.Axis.Recovery.rotation_square_sub_transpose,
              Geometry.Rotations.Axis.Recovery.transpose_square_sub_rotation]
    _ = Matrix3.scale (1 + Matrix3.trace rotation.matrix)
        (Matrix3.sub
          (Matrix3.add rotation.matrix
            (Matrix3.transpose rotation.matrix))
          (Matrix3.scale 2 Matrix3.identity)) := by
            ext <;> unfold Matrix3.add Matrix3.sub Matrix3.scale
              Matrix3.identity <;> ring1

/-- A rotation of half spread one is symmetric. This is the finite classification step invoked, but not supplied, by the
paper's proof of Theorem 40. -/
theorem rotation_isSymmetric_of_halfSpread_eq_one [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K) (halfTurnSpread : Spread.halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.IsSymmetric rotation.matrix := by
  have traceValue := Geometry.Rotations.Axis.Recovery.trace_eq_neg_one_of_halfSpread_eq_one rotation
    halfTurnSpread twoNonzero
  have squareZero := Geometry.Rotations.Axis.Recovery.rotationAntisymmetricNumerator_square rotation
  rw [traceValue] at squareZero
  have numeratorSquareZero :
      Matrix3.mul
          (Matrix3.sub rotation.matrix
            (Matrix3.transpose rotation.matrix))
          (Matrix3.sub rotation.matrix
            (Matrix3.transpose rotation.matrix)) =
        Matrix3.zero := by
    calc
      Matrix3.mul
          (Matrix3.sub rotation.matrix
            (Matrix3.transpose rotation.matrix))
          (Matrix3.sub rotation.matrix
            (Matrix3.transpose rotation.matrix)) =
        Matrix3.scale (1 + (-1 : K))
          (Matrix3.sub
            (Matrix3.add rotation.matrix
              (Matrix3.transpose rotation.matrix))
            (Matrix3.scale 2 Matrix3.identity)) := squareZero
      _ = Matrix3.zero := by
        ext <;> unfold Matrix3.scale Matrix3.zero <;> ring1
  have numeratorAntisymmetric :
      Matrix3.IsAntisymmetric
        (Matrix3.sub rotation.matrix
          (Matrix3.transpose rotation.matrix)) := by
    unfold Matrix3.IsAntisymmetric
    rw [Matrix3.transpose_sub, Matrix3.transpose_transpose]
    ext <;> unfold Matrix3.sub Matrix3.neg <;> ring1
  have numeratorZero := Purelib.LinearAlgebra.Coordinates3.Antisymmetric.antisymmetric_eq_zero_of_square_eq_zero
    (Matrix3.sub rotation.matrix (Matrix3.transpose rotation.matrix))
    twoNonzero numeratorAntisymmetric numeratorSquareZero
  unfold Matrix3.IsSymmetric
  exact (Matrix3.eq_of_sub_eq_zero numeratorZero).symm

/-- The symmetric idempotent projector onto the axis of a half turn. -/
@[expose] public def halfTurnProjector (rotation : Rotations.Basic.Rotation K) : Coordinates3.Matrix3 K :=
  Matrix3.scale (1 / 2)
    (Matrix3.add Matrix3.identity rotation.matrix)

/-- The projector associated with a half-spread-one rotation is symmetric. -/
private theorem halfTurnProjector_isSymmetric [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K) (halfTurnSpread : Spread.halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    (Geometry.Rotations.Axis.Recovery.halfTurnProjector rotation).IsSymmetric := by
  have rotationSymmetric := Geometry.Rotations.Axis.Recovery.rotation_isSymmetric_of_halfSpread_eq_one
    rotation halfTurnSpread twoNonzero
  unfold Matrix3.IsSymmetric Geometry.Rotations.Axis.Recovery.halfTurnProjector at *
  rw [Matrix3.transpose_scale, Matrix3.transpose_add,
    Matrix3.transpose_identity, rotationSymmetric]

/-- The projector associated with a half-spread-one rotation is idempotent. -/
private theorem halfTurnProjector_idempotent [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K) (halfTurnSpread : Spread.halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.mul (Geometry.Rotations.Axis.Recovery.halfTurnProjector rotation)
      (Geometry.Rotations.Axis.Recovery.halfTurnProjector rotation) =
      Geometry.Rotations.Axis.Recovery.halfTurnProjector rotation := by
  have symmetric := Geometry.Rotations.Axis.Recovery.rotation_isSymmetric_of_halfSpread_eq_one rotation
    halfTurnSpread twoNonzero
  have rotationSquare :
      Matrix3.mul rotation.matrix rotation.matrix = Matrix3.identity := by
    unfold Matrix3.IsSymmetric at symmetric
    calc
      Matrix3.mul rotation.matrix rotation.matrix =
          Matrix3.mul rotation.matrix
            (Matrix3.transpose rotation.matrix) := by rw [symmetric]
      _ = Matrix3.identity := rotation.orthogonal
  have twoCancel := Algebra.Field.ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  have coefficient :
      (1 / 2 : K) * (1 / 2) * 2 = 1 / 2 := by
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      1 * (2 : K)⁻¹ * (1 * (2 : K)⁻¹) * 2 =
          (2 : K)⁻¹ * (2 * (2 : K)⁻¹) := by ring1
      _ = 1 * (2 : K)⁻¹ := by rw [twoCancel, mul_one, one_mul]
  unfold Geometry.Rotations.Axis.Recovery.halfTurnProjector
  rw [Matrix3.mul_scale_left, Matrix3.mul_scale_right,
    Matrix3.scale_scale, Matrix3.mul_add_left, Matrix3.mul_add_right,
    Matrix3.mul_add_right, Matrix3.identity_mul, Matrix3.identity_mul,
    Matrix3.mul_identity, rotationSquare]
  rw [show Matrix3.add
      (Matrix3.add Matrix3.identity rotation.matrix)
      (Matrix3.add rotation.matrix Matrix3.identity) =
        Matrix3.scale 2
          (Matrix3.add Matrix3.identity rotation.matrix) by
      ext <;> unfold Matrix3.add Matrix3.scale Matrix3.identity <;> ring1,
    Matrix3.scale_scale, coefficient]

/-- The projector associated with a half-spread-one rotation has trace one. -/
private theorem halfTurnProjector_trace [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K) (halfTurnSpread : Spread.halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.trace (Geometry.Rotations.Axis.Recovery.halfTurnProjector rotation) = 1 := by
  have traceValue := Geometry.Rotations.Axis.Recovery.trace_eq_neg_one_of_halfSpread_eq_one rotation
    halfTurnSpread twoNonzero
  have twoCancel := Algebra.Field.ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  unfold Geometry.Rotations.Axis.Recovery.halfTurnProjector
  rw [Matrix3.trace_scale, Matrix3.trace_add, traceValue]
  unfold Matrix3.trace Matrix3.identity
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    (1 * (2 : K)⁻¹) * (1 + 1 + 1 + -1) =
        2 * (2 : K)⁻¹ := by ring1
    _ = 1 := twoCancel

/-- The projector associated with a half-spread-one rotation has zero adjugate. -/
private theorem halfTurnProjector_adjugate [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K) (halfTurnSpread : Spread.halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.adjugate (Geometry.Rotations.Axis.Recovery.halfTurnProjector rotation) = Matrix3.zero := by
  let projector := Geometry.Rotations.Axis.Recovery.halfTurnProjector rotation
  have idempotent : Matrix3.mul projector projector = projector := by
    unfold projector
    exact Geometry.Rotations.Axis.Recovery.halfTurnProjector_idempotent rotation halfTurnSpread
      twoNonzero
  have traceOne : Matrix3.trace projector = 1 := by
    unfold projector
    exact Geometry.Rotations.Axis.Recovery.halfTurnProjector_trace rotation halfTurnSpread twoNonzero
  have traceSquare := congrArg Matrix3.trace idempotent
  rw [Matrix3.trace_square, traceOne] at traceSquare
  have principalZero : Matrix3.principalTrace projector = 0 := by
    apply (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] (twoNonzero : (2 : K) ≠ 0) {value : K} (twiceZero :
      2 * value = 0) => (Purelib.Algebra.Field.Characteristic.Nonzero.eq_zero_of_two_mul_eq_zero (K := K) twoNonzero
      value twiceZero : value = 0)) twoNonzero
    calc
      2 * Matrix3.principalTrace projector =
          1 ^ 2 -
            (1 ^ 2 - 2 * Matrix3.principalTrace projector) := by ring1
      _ = 0 := by rw [traceSquare]; ring1
  rw [Matrix3.adjugate_expansion, idempotent, traceOne, principalZero]
  ext <;> unfold Matrix3.add Matrix3.sub Matrix3.scale Matrix3.identity
    Matrix3.zero <;> ring1

/-- Collect symmetry, idempotence, trace one, and zero adjugate for the half-turn projector.

The rotation has half spread one and two is nonzero in the coefficient field. -/
theorem halfTurnProjector_certificates [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K)
    (halfTurnSpread : Spread.halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    (Geometry.Rotations.Axis.Recovery.halfTurnProjector rotation).IsSymmetric ∧
      Matrix3.mul (Geometry.Rotations.Axis.Recovery.halfTurnProjector rotation)
        (Geometry.Rotations.Axis.Recovery.halfTurnProjector rotation) =
        Geometry.Rotations.Axis.Recovery.halfTurnProjector rotation ∧
      Matrix3.trace (Geometry.Rotations.Axis.Recovery.halfTurnProjector rotation) = 1 ∧
      Matrix3.adjugate (Geometry.Rotations.Axis.Recovery.halfTurnProjector rotation) = Matrix3.zero := by
  exact ⟨Geometry.Rotations.Axis.Recovery.halfTurnProjector_isSymmetric rotation halfTurnSpread
    twoNonzero,
    Geometry.Rotations.Axis.Recovery.halfTurnProjector_idempotent rotation halfTurnSpread twoNonzero,
    Geometry.Rotations.Axis.Recovery.halfTurnProjector_trace rotation halfTurnSpread twoNonzero,
    Geometry.Rotations.Axis.Recovery.halfTurnProjector_adjugate rotation halfTurnSpread twoNonzero⟩

/-- The cached non-null axis extracted from a half-spread-one rotation. -/
@[expose] public def halfTurnAxisWitness [DecidableEq K] (rotation : Rotations.Basic.Rotation K)
    (halfTurnSpread : Spread.halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Projector.RankOneProjectorWitness (Geometry.Rotations.Axis.Recovery.halfTurnProjector rotation) :=
  let certificates := Geometry.Rotations.Axis.Recovery.halfTurnProjector_certificates rotation halfTurnSpread twoNonzero
  Projector.rankOneProjectorWitness (Geometry.Rotations.Axis.Recovery.halfTurnProjector rotation)
    certificates.1 certificates.2.1 certificates.2.2.1 certificates.2.2.2
    twoNonzero

/-- The executable axis vector selected for a half-spread-one rotation. -/
@[expose] public def halfTurnAxis [DecidableEq K] (rotation : Rotations.Basic.Rotation K)
    (halfTurnSpread : Spread.halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) : Coordinates3.Vector K :=
  (Geometry.Rotations.Axis.Recovery.halfTurnAxisWitness rotation halfTurnSpread twoNonzero).vector

/-- The selected half-turn axis has nonzero quadrance. -/
theorem halfTurnAxis_nonNull [DecidableEq K] (rotation : Rotations.Basic.Rotation K)
    (halfTurnSpread : Spread.halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    (Geometry.Rotations.Axis.Recovery.halfTurnAxis rotation halfTurnSpread twoNonzero).quadrance ≠ 0 :=
  (Geometry.Rotations.Axis.Recovery.halfTurnAxisWitness rotation halfTurnSpread twoNonzero).nonNull

/-- The half-turn projector is the outer product of its selected axis divided by the axis quadrance. -/
theorem halfTurnProjector_eq_axisOuter [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K) (halfTurnSpread : Spread.halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Geometry.Rotations.Axis.Recovery.halfTurnProjector rotation =
      Matrix3.scale
        (1 / (Geometry.Rotations.Axis.Recovery.halfTurnAxis rotation halfTurnSpread twoNonzero).quadrance)
        (Matrix3.outer
          (Geometry.Rotations.Axis.Recovery.halfTurnAxis rotation halfTurnSpread twoNonzero)
          (Geometry.Rotations.Axis.Recovery.halfTurnAxis rotation halfTurnSpread twoNonzero)) :=
  (Geometry.Rotations.Axis.Recovery.halfTurnAxisWitness rotation halfTurnSpread twoNonzero).reconstruction

/-- Twice the half-turn projector equals `I + R` when two is nonzero. -/
theorem halfTurnProjector_doubled (rotation : Rotations.Basic.Rotation K)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.scale 2 (Geometry.Rotations.Axis.Recovery.halfTurnProjector rotation) =
      Matrix3.add Matrix3.identity rotation.matrix := by
  have twoCancel := Algebra.Field.ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  unfold Geometry.Rotations.Axis.Recovery.halfTurnProjector
  rw [Matrix3.scale_scale]
  have coefficient : (2 : K) * (1 / 2) = 1 := by
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    rw [one_mul, twoCancel]
  rw [coefficient]
  ext <;> unfold Matrix3.scale <;> ring1

/-- Constructive classification of the missing case in the paper: every rotation with half spread one is the half turn
about its selected non-null axis. -/
theorem rotation_eq_halfTurn_halfTurnAxis [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K) (halfTurnSpread : Spread.halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    rotation.matrix =
      Reflection.halfTurn (Geometry.Rotations.Axis.Recovery.halfTurnAxis rotation halfTurnSpread twoNonzero)
        (Geometry.Rotations.Axis.Recovery.halfTurnAxis_nonNull rotation halfTurnSpread twoNonzero) := by
  let axis := Geometry.Rotations.Axis.Recovery.halfTurnAxis rotation halfTurnSpread twoNonzero
  let axisNonNull := Geometry.Rotations.Axis.Recovery.halfTurnAxis_nonNull rotation halfTurnSpread twoNonzero
  have projectorForm :
      Geometry.Rotations.Axis.Recovery.halfTurnProjector rotation =
        Matrix3.scale (1 / axis.quadrance) (Matrix3.outer axis axis) := by
    unfold axis
    exact Geometry.Rotations.Axis.Recovery.halfTurnProjector_eq_axisOuter rotation halfTurnSpread twoNonzero
  calc
    rotation.matrix =
        Matrix3.sub
          (Matrix3.add Matrix3.identity rotation.matrix)
          Matrix3.identity := by
            ext <;> unfold Matrix3.add Matrix3.sub Matrix3.identity <;> ring1
    _ = Matrix3.sub
        (Matrix3.scale 2 (Geometry.Rotations.Axis.Recovery.halfTurnProjector rotation))
        Matrix3.identity := by
          rw [Geometry.Rotations.Axis.Recovery.halfTurnProjector_doubled rotation twoNonzero]
    _ = Matrix3.sub
        (Matrix3.scale 2
          (Matrix3.scale (1 / axis.quadrance)
            (Matrix3.outer axis axis)))
        Matrix3.identity := by rw [projectorForm]
    _ = Reflection.halfTurn axis axisNonNull := by
      unfold Reflection.halfTurn Reflection.reflection
      ext <;> unfold Matrix3.sub Matrix3.neg Matrix3.scale Matrix3.identity
        Matrix3.outer <;>
        simp only [Algebra.Field.ExplicitField.div_eq_mul_inv] <;> ring1

/-! ### A uniform constructive axis and spread witness -/

/-- The two finite charts used by the canonical axis construction. Each branch stores the denominator or non-nullness
certificate needed to evaluate its displayed matrix, together with the equality identifying that matrix with the
supplied rotation. -/
inductive RotationAxisChart (rotation : Rotations.Basic.Rotation K) (axis : Coordinates3.Vector K) where
  /-- Retain the non-half-turn chart, cap denominator, and equality of the cap matrix with the rotation. -/ | affine
      (notHalfTurn : Spread.halfSpread rotation ≠ 1)
      (defined : Cap.capDenominator axis ≠ 0)
      (matrix_eq : rotation.matrix = Cap.cap axis defined)
  /-- Retain the half-spread-one chart, non-null axis, and equality of the half-turn matrix with the rotation. -/ |
    halfTurn
      (halfTurnSpread : Spread.halfSpread rotation = 1)
      (axisNonNull : axis.quadrance ≠ 0)
      (matrix_eq : rotation.matrix = Reflection.halfTurn axis axisNonNull)

set_option genInjectivity false in
/-- Cached canonical axis, chart, and geometric spread data for an arbitrary rotation. Downstream constructions can
consume the selected axis and perpendicular direction without repeating the half-spread test, projector calculation, or
perpendicular search. -/
structure RotationAxisSpreadWitness (rotation : Rotations.Basic.Rotation K) where
  /-- The cached axis selected for the original rotation. -/ axis : Coordinates3.Vector K
  /-- The cached perpendicular direction used to measure spread. -/ direction : Coordinates3.Vector K
  /-- The cached test direction has nonzero quadrance. -/ directionNonNull : direction.quadrance ≠ 0
  /-- The cached test direction is perpendicular to the retained axis. -/ directionPerpendicular :
    direction.Perpendicular axis
  /-- The retained affine or half-turn chart certificate for this rotation and axis. -/ chart :
    Geometry.Rotations.Axis.Recovery.RotationAxisChart rotation axis
  /-- The cached test direction computes the trace-defined rotation spread. -/ spread_eq :
    Spread.rotationSpreadAt rotation direction directionNonNull =
      Spread.rotationSpread rotation

constructive_injectivity RotationAxisSpreadWitness

/-- Construct the canonical axis and spread witness for every rotation by one decidable chart split. -/
@[expose] public def rotationAxisSpreadWitness [DecidableEq K] (rotation : Rotations.Basic.Rotation K)
    (twoNonzero : (2 : K) ≠ 0) :
    Geometry.Rotations.Axis.Recovery.RotationAxisSpreadWitness rotation := by
  by_cases halfTurnSpread : Spread.halfSpread rotation = 1
  · let axis := Geometry.Rotations.Axis.Recovery.halfTurnAxis rotation halfTurnSpread twoNonzero
    let axisNonNull := Geometry.Rotations.Axis.Recovery.halfTurnAxis_nonNull rotation halfTurnSpread twoNonzero
    let chosen := Perpendicular.perpendicularNonNullWitness axis twoNonzero
    have matrixEq : rotation.matrix = Reflection.halfTurn axis axisNonNull := by
      unfold axis axisNonNull
      exact Geometry.Rotations.Axis.Recovery.rotation_eq_halfTurn_halfTurnAxis rotation halfTurnSpread
        twoNonzero
    have rotationEq :
        rotation = Reflection.halfTurnRotation axis axisNonNull :=
      Geometry.Rotations.Basic.Rotation.eq_of_matrix_eq rotation (Reflection.halfTurnRotation axis axisNonNull)
        matrixEq
    refine
      { axis := axis
        direction := chosen.value
        directionNonNull := chosen.nonNull
        directionPerpendicular := chosen.perpendicular
        chart := Geometry.Rotations.Axis.Recovery.RotationAxisChart.halfTurn halfTurnSpread axisNonNull matrixEq
        spread_eq := ?_ }
    rw [rotationEq]
    exact Spread.rotationSpreadAt_halfTurn axis axisNonNull twoNonzero chosen.value
      chosen.nonNull chosen.perpendicular
  · let axis := Geometry.Rotations.Axis.Recovery.rotationAnchorVector rotation halfTurnSpread
    let defined := Geometry.Rotations.Axis.Recovery.rotationAnchorVector_capDefined rotation halfTurnSpread
      twoNonzero
    let chosen := Perpendicular.perpendicularNonNullWitness axis twoNonzero
    have matrixEq : rotation.matrix = Cap.cap axis defined := by
      unfold axis defined
      exact (Geometry.Rotations.Axis.Recovery.cap_rotationAnchor rotation halfTurnSpread twoNonzero).symm
    have rotationEq : rotation = Cap.capRotation axis defined :=
      Geometry.Rotations.Basic.Rotation.eq_of_matrix_eq rotation (Cap.capRotation axis defined) matrixEq
    refine
      { axis := axis
        direction := chosen.value
        directionNonNull := chosen.nonNull
        directionPerpendicular := chosen.perpendicular
        chart := Geometry.Rotations.Axis.Recovery.RotationAxisChart.affine halfTurnSpread defined matrixEq
        spread_eq := ?_ }
    rw [rotationEq]
    exact Spread.rotationSpreadAt_cap axis defined twoNonzero chosen.value
      chosen.nonNull chosen.perpendicular

/-- The canonical axis selected by `rotationAxisSpreadWitness`. -/
@[expose] public def canonicalRotationAxis [DecidableEq K] (rotation : Rotations.Basic.Rotation K)
    (twoNonzero : (2 : K) ≠ 0) : Coordinates3.Vector K :=
  (Geometry.Rotations.Axis.Recovery.rotationAxisSpreadWitness rotation twoNonzero).axis

/-- The canonical non-null perpendicular direction selected for a rotation. -/
@[expose] public def canonicalRotationSpreadDirection [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K) (twoNonzero : (2 : K) ≠ 0) : Coordinates3.Vector K :=
  (Geometry.Rotations.Axis.Recovery.rotationAxisSpreadWitness rotation twoNonzero).direction

/-- The canonical spread direction has nonzero quadrance. -/
theorem canonicalRotationSpreadDirection_nonNull [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    (Geometry.Rotations.Axis.Recovery.canonicalRotationSpreadDirection rotation twoNonzero).quadrance ≠ 0 :=
  (Geometry.Rotations.Axis.Recovery.rotationAxisSpreadWitness rotation twoNonzero).directionNonNull

/-- The canonical spread direction is perpendicular to the selected rotation axis. -/
theorem canonicalRotationSpreadDirection_perpendicular [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    (Geometry.Rotations.Axis.Recovery.canonicalRotationSpreadDirection rotation twoNonzero).Perpendicular
      (Geometry.Rotations.Axis.Recovery.canonicalRotationAxis rotation twoNonzero) :=
  (Geometry.Rotations.Axis.Recovery.rotationAxisSpreadWitness rotation twoNonzero).directionPerpendicular

/-- Uniform form of Theorem 31: the geometric spread computed from the canonical perpendicular direction agrees with the
trace expression for every rotation. -/
theorem rotationSpreadAt_canonical [DecidableEq K] (rotation : Rotations.Basic.Rotation K)
    (twoNonzero : (2 : K) ≠ 0) :
    Spread.rotationSpreadAt rotation
        (Geometry.Rotations.Axis.Recovery.canonicalRotationSpreadDirection rotation twoNonzero)
        (Geometry.Rotations.Axis.Recovery.canonicalRotationSpreadDirection_nonNull rotation twoNonzero) =
      Spread.rotationSpread rotation :=
  (Geometry.Rotations.Axis.Recovery.rotationAxisSpreadWitness rotation twoNonzero).spread_eq

/-- The uniform canonical-direction theorem with the second spread polynomial exposed directly, rather than through the
`rotationSpread` abbreviation. -/
theorem rotationSpreadAt_canonical_eq_halfSpreadPolynomial [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    Spread.rotationSpreadAt rotation
        (Geometry.Rotations.Axis.Recovery.canonicalRotationSpreadDirection rotation twoNonzero)
        (Geometry.Rotations.Axis.Recovery.canonicalRotationSpreadDirection_nonNull rotation twoNonzero) =
      4 * Spread.halfSpread rotation * (1 - Spread.halfSpread rotation) := by
  rw [Geometry.Rotations.Axis.Recovery.rotationSpreadAt_canonical rotation twoNonzero]
  rfl

/-- Affine-chart projection of the uniform witness: after exposing its cached chart certificate, the spread theorem is
exactly the existing cap theorem. -/
theorem RotationAxisSpreadWitness.affine_spread_projection
    {rotation : Rotations.Basic.Rotation K} (witness : Geometry.Rotations.Axis.Recovery.RotationAxisSpreadWitness
      rotation)
    (twoNonzero : (2 : K) ≠ 0)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (defined : Cap.capDenominator witness.axis ≠ 0)
    (matrixEq : rotation.matrix = Cap.cap witness.axis defined)
    (_chartEq : witness.chart =
      Geometry.Rotations.Axis.Recovery.RotationAxisChart.affine notHalfTurn defined matrixEq) :
    Spread.rotationSpreadAt rotation witness.direction witness.directionNonNull =
      Spread.rotationSpread (Cap.capRotation witness.axis defined) := by
  calc
    Spread.rotationSpreadAt rotation witness.direction witness.directionNonNull =
        Spread.rotationSpreadAt (Cap.capRotation witness.axis defined)
          witness.direction witness.directionNonNull := by
      unfold Spread.rotationSpreadAt Coordinates3.Vector.spread
      rw [matrixEq]
      rfl
    _ = Spread.rotationSpread (Cap.capRotation witness.axis defined) :=
      Spread.rotationSpreadAt_cap witness.axis defined twoNonzero witness.direction
        witness.directionNonNull witness.directionPerpendicular

/-- Half-turn-chart projection of the uniform witness: after exposing its cached chart certificate, the spread theorem
is exactly the existing half-turn theorem. -/
theorem RotationAxisSpreadWitness.halfTurn_spread_projection
    {rotation : Rotations.Basic.Rotation K} (witness : Geometry.Rotations.Axis.Recovery.RotationAxisSpreadWitness
      rotation)
    (twoNonzero : (2 : K) ≠ 0)
    (halfTurnSpread : Spread.halfSpread rotation = 1)
    (axisNonNull : witness.axis.quadrance ≠ 0)
    (matrixEq : rotation.matrix = Reflection.halfTurn witness.axis axisNonNull)
    (_chartEq : witness.chart =
      Geometry.Rotations.Axis.Recovery.RotationAxisChart.halfTurn halfTurnSpread axisNonNull matrixEq) :
    Spread.rotationSpreadAt rotation witness.direction witness.directionNonNull =
      Spread.rotationSpread (Reflection.halfTurnRotation witness.axis axisNonNull) := by
  calc
    Spread.rotationSpreadAt rotation witness.direction witness.directionNonNull =
        Spread.rotationSpreadAt (Reflection.halfTurnRotation witness.axis axisNonNull)
          witness.direction witness.directionNonNull := by
      unfold Spread.rotationSpreadAt Coordinates3.Vector.spread
      rw [matrixEq]
      rfl
    _ = Spread.rotationSpread (Reflection.halfTurnRotation witness.axis axisNonNull) :=
      Spread.rotationSpreadAt_halfTurn witness.axis axisNonNull twoNonzero
        witness.direction witness.directionNonNull
        witness.directionPerpendicular

/-- Every admissible perpendicular direction to the canonical axis computes the same rotation spread. -/
theorem rotationSpreadAt_canonicalAxis [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K) (twoNonzero : (2 : K) ≠ 0)
    (direction : Coordinates3.Vector K) (directionNonNull : direction.quadrance ≠ 0)
    (perpendicular :
      direction.Perpendicular (Geometry.Rotations.Axis.Recovery.canonicalRotationAxis rotation twoNonzero)) :
    Spread.rotationSpreadAt rotation direction directionNonNull =
      Spread.rotationSpread rotation := by
  let witness := Geometry.Rotations.Axis.Recovery.rotationAxisSpreadWitness rotation twoNonzero
  change direction.Perpendicular witness.axis at perpendicular
  change Spread.rotationSpreadAt rotation direction directionNonNull =
    Spread.rotationSpread rotation
  cases witness.chart with
  | affine notHalfTurn defined matrixEq =>
      have rotationEq : rotation = Cap.capRotation witness.axis defined :=
        Geometry.Rotations.Basic.Rotation.eq_of_matrix_eq rotation
          (Cap.capRotation witness.axis defined) matrixEq
      rw [rotationEq]
      exact Spread.rotationSpreadAt_cap witness.axis defined twoNonzero direction
        directionNonNull perpendicular
  | halfTurn halfTurnSpread axisNonNull matrixEq =>
      have rotationEq : rotation = Reflection.halfTurnRotation witness.axis axisNonNull :=
        Geometry.Rotations.Basic.Rotation.eq_of_matrix_eq rotation
          (Reflection.halfTurnRotation witness.axis axisNonNull) matrixEq
      rw [rotationEq]
      exact Spread.rotationSpreadAt_halfTurn witness.axis axisNonNull twoNonzero
        direction directionNonNull perpendicular

/-- Choice independence for the uniform form of Definition 30. -/
theorem rotationSpreadAt_canonicalAxis_independent [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K) (twoNonzero : (2 : K) ≠ 0)
    (first second : Coordinates3.Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0)
    (firstPerpendicular :
      first.Perpendicular (Geometry.Rotations.Axis.Recovery.canonicalRotationAxis rotation twoNonzero))
    (secondPerpendicular :
      second.Perpendicular (Geometry.Rotations.Axis.Recovery.canonicalRotationAxis rotation twoNonzero)) :
    Spread.rotationSpreadAt rotation first firstNonNull =
      Spread.rotationSpreadAt rotation second secondNonNull := by
  rw [Geometry.Rotations.Axis.Recovery.rotationSpreadAt_canonicalAxis rotation twoNonzero first firstNonNull
      firstPerpendicular,
    Geometry.Rotations.Axis.Recovery.rotationSpreadAt_canonicalAxis rotation twoNonzero second secondNonNull
      secondPerpendicular]

/-! ### The two constructive factorization branches -/

/-- The second mirror normal for a half turn, determined by the axis and the freely chosen first mirror normal. -/
@[expose] public def halfTurnSecondMirror (axis first : Coordinates3.Vector K) : Coordinates3.Vector K :=
  Coordinates3.Vector.cross axis first

/-- The second mirror's quadrance is the product of the perpendicular axis and first-mirror quadrances. -/
private theorem quadrance_halfTurnSecondMirror (axis first : Coordinates3.Vector K)
    (perpendicular : first.Perpendicular axis) :
    (Geometry.Rotations.Axis.Recovery.halfTurnSecondMirror axis first).quadrance =
      axis.quadrance * first.quadrance := by
  have dotZero : Coordinates3.Vector.dot axis first = 0 := by
    rw [Coordinates3.Vector.dot_comm]
    exact perpendicular
  have lagrange := Coordinates3.Vector.lagrange axis first
  rw [dotZero] at lagrange
  unfold Geometry.Rotations.Axis.Recovery.halfTurnSecondMirror
  calc
    (Coordinates3.Vector.cross axis first).quadrance =
        0 ^ 2 + (Coordinates3.Vector.cross axis first).quadrance := by ring1
    _ = axis.quadrance * first.quadrance := lagrange

/-- A non-null axis and non-null perpendicular first mirror give a non-null second mirror. -/
theorem halfTurnSecondMirror_nonNull (axis first : Coordinates3.Vector K)
    (axisNonNull : axis.quadrance ≠ 0)
    (firstNonNull : first.quadrance ≠ 0)
    (perpendicular : first.Perpendicular axis) :
    (Geometry.Rotations.Axis.Recovery.halfTurnSecondMirror axis first).quadrance ≠ 0 := by
  rw [Geometry.Rotations.Axis.Recovery.quadrance_halfTurnSecondMirror axis first perpendicular]
  exact Algebra.Field.ExplicitField.mul_ne_zero axisNonNull firstNonNull

/-- The weighted outer products of a perpendicular axis, first mirror, and their cross product sum to the quadrance
product times the identity. -/
private theorem orthogonal_outer_decomposition (axis first : Coordinates3.Vector K)
    (perpendicular : first.Perpendicular axis) :
    Matrix3.add
        (Matrix3.add
          (Matrix3.scale first.quadrance (Matrix3.outer axis axis))
          (Matrix3.scale axis.quadrance (Matrix3.outer first first)))
        (Matrix3.outer (Geometry.Rotations.Axis.Recovery.halfTurnSecondMirror axis first)
          (Geometry.Rotations.Axis.Recovery.halfTurnSecondMirror axis first)) =
      Matrix3.scale (axis.quadrance * first.quadrance)
        Matrix3.identity := by
  have dotZero : Coordinates3.Vector.dot axis first = 0 := by
    rw [Coordinates3.Vector.dot_comm]
    exact perpendicular
  unfold Geometry.Rotations.Axis.Recovery.halfTurnSecondMirror
  rw [Matrix3.outer_cross_self, dotZero]
  ext <;> unfold Matrix3.add Matrix3.sub Matrix3.scale Matrix3.identity <;>
    ring1

/-- The three normalized outer products of a non-null perpendicular pair and their cross product sum to the identity. -/
private theorem normalized_orthogonal_outer_decomposition
    (axis first : Coordinates3.Vector K)
    (axisNonNull : axis.quadrance ≠ 0)
    (firstNonNull : first.quadrance ≠ 0)
    (perpendicular : first.Perpendicular axis) :
    Matrix3.add
        (Matrix3.add
          (Matrix3.scale (1 / axis.quadrance) (Matrix3.outer axis axis))
          (Matrix3.scale (1 / first.quadrance)
            (Matrix3.outer first first)))
        (Matrix3.scale
          (1 / (Geometry.Rotations.Axis.Recovery.halfTurnSecondMirror axis first).quadrance)
          (Matrix3.outer (Geometry.Rotations.Axis.Recovery.halfTurnSecondMirror axis first)
            (Geometry.Rotations.Axis.Recovery.halfTurnSecondMirror axis first))) =
      Matrix3.identity := by
  let product := axis.quadrance * first.quadrance
  have productNonzero : product ≠ 0 :=
    Algebra.Field.ExplicitField.mul_ne_zero axisNonNull firstNonNull
  have productCancel := Algebra.Field.ExplicitField.mul_inv_cancel product productNonzero
  have productInverseCancel : product⁻¹ * product = 1 := by
    calc
      product⁻¹ * product = product * product⁻¹ := by ring1
      _ = 1 := productCancel
  have axisCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    axis.quadrance axisNonNull
  have firstCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    first.quadrance firstNonNull
  have productInverse := Purelib.Algebra.Field.Inverse.inverse_product axisNonNull
    firstNonNull
  have secondQuadrance := Geometry.Rotations.Axis.Recovery.quadrance_halfTurnSecondMirror axis first
    perpendicular
  have axisCoefficient : product⁻¹ * first.quadrance = axis.quadrance⁻¹ := by
    unfold product
    rw [productInverse]
    calc
      axis.quadrance⁻¹ * first.quadrance⁻¹ * first.quadrance =
          axis.quadrance⁻¹ *
            (first.quadrance * first.quadrance⁻¹) := by ring1
      _ = axis.quadrance⁻¹ := by rw [firstCancel, mul_one]
  have firstCoefficient : product⁻¹ * axis.quadrance = first.quadrance⁻¹ := by
    unfold product
    rw [productInverse]
    calc
      axis.quadrance⁻¹ * first.quadrance⁻¹ * axis.quadrance =
          first.quadrance⁻¹ *
            (axis.quadrance * axis.quadrance⁻¹) := by ring1
      _ = first.quadrance⁻¹ := by rw [axisCancel, mul_one]
  have secondCoefficient :
      product⁻¹ = (Geometry.Rotations.Axis.Recovery.halfTurnSecondMirror axis first).quadrance⁻¹ := by
    rw [secondQuadrance]
  have base := Geometry.Rotations.Axis.Recovery.orthogonal_outer_decomposition axis first perpendicular
  have scaled := congrArg (Matrix3.scale product⁻¹) base
  rw [Matrix3.scale_add, Matrix3.scale_add,
    Matrix3.scale_scale, Matrix3.scale_scale, Matrix3.scale_scale,
    axisCoefficient, firstCoefficient, productInverseCancel,
    secondCoefficient, Matrix3.one_scale] at scaled
  simpa only [Algebra.Field.ExplicitField.div_eq_mul_inv, one_mul] using scaled

/-- Perpendicular non-null mirrors compose to the half turn about their cross-product axis, with the second mirror
determined by the selected axis and first mirror. -/
theorem reflection_mul_halfTurnSecondMirror (axis first : Coordinates3.Vector K)
    (axisNonNull : axis.quadrance ≠ 0)
    (firstNonNull : first.quadrance ≠ 0)
    (perpendicular : first.Perpendicular axis) :
    Matrix3.mul (Reflection.reflection first firstNonNull)
        (Reflection.reflection (Geometry.Rotations.Axis.Recovery.halfTurnSecondMirror axis first)
          (Geometry.Rotations.Axis.Recovery.halfTurnSecondMirror_nonNull axis first axisNonNull firstNonNull
            perpendicular)) =
      Reflection.halfTurn axis axisNonNull := by
  let second := Geometry.Rotations.Axis.Recovery.halfTurnSecondMirror axis first
  let secondNonNull := Geometry.Rotations.Axis.Recovery.halfTurnSecondMirror_nonNull axis first axisNonNull
    firstNonNull perpendicular
  have firstSecondDot : Coordinates3.Vector.dot first second = 0 := by
    unfold second Geometry.Rotations.Axis.Recovery.halfTurnSecondMirror
    rw [Coordinates3.Vector.dot_comm]
    exact Coordinates3.Vector.cross_dot_right axis first
  have outerProductZero :
      Matrix3.mul (Matrix3.outer first first)
          (Matrix3.outer second second) = Matrix3.zero := by
    rw [Matrix3.mul_outer, firstSecondDot]
    ext <;> unfold Matrix3.scale Matrix3.zero <;> ring1
  have expanded :
      Matrix3.mul (Reflection.reflection first firstNonNull)
          (Reflection.reflection second secondNonNull) =
        Matrix3.sub
          (Matrix3.sub Matrix3.identity
            (Matrix3.scale (2 / first.quadrance)
              (Matrix3.outer first first)))
          (Matrix3.scale (2 / second.quadrance)
            (Matrix3.outer second second)) := by
    unfold Reflection.reflection
    rw [Matrix3.mul_sub_right, Matrix3.mul_identity,
      Matrix3.mul_scale_right, Matrix3.mul_sub_left,
      Matrix3.identity_mul, Matrix3.mul_scale_left, outerProductZero]
    ext <;> unfold Matrix3.sub Matrix3.scale Matrix3.zero <;> ring1
  rw [expanded]
  have decomposition := Geometry.Rotations.Axis.Recovery.normalized_orthogonal_outer_decomposition axis
    first
    axisNonNull firstNonNull perpendicular
  unfold second at *
  unfold Reflection.halfTurn Reflection.reflection
  rw [← decomposition]
  ext <;> unfold Matrix3.add Matrix3.sub Matrix3.neg Matrix3.scale <;>
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv] <;> ring1

/-- Theorem 40's determined second mirror in the affine anchor chart. -/
@[expose] public def capSecondMirror (anchorVector first : Coordinates3.Vector K) : Coordinates3.Vector K :=
  Coordinates3.Vector.add first (Coordinates3.Vector.cross anchorVector first)

/-- The first mirror dotted with the cap's second mirror is the first mirror quadrance. -/
theorem dot_capSecondMirror (anchorVector first : Coordinates3.Vector K) :
    Coordinates3.Vector.dot first (Geometry.Rotations.Axis.Recovery.capSecondMirror anchorVector first) =
      first.quadrance := by
  unfold Geometry.Rotations.Axis.Recovery.capSecondMirror
  rw [Coordinates3.Vector.dot_add_right]
  have crossDot : Coordinates3.Vector.dot first (Coordinates3.Vector.cross anchorVector first) = 0 := by
    rw [Coordinates3.Vector.dot_comm]
    exact Coordinates3.Vector.cross_dot_right anchorVector first
  rw [crossDot]
  unfold Coordinates3.Vector.quadrance
  ring1

/-- For a perpendicular first mirror, its cross product with the second mirror is the anchor scaled by the first
quadrance. -/
theorem cross_capSecondMirror (anchorVector first : Coordinates3.Vector K)
    (perpendicular : first.Perpendicular anchorVector) :
    Coordinates3.Vector.cross first (Geometry.Rotations.Axis.Recovery.capSecondMirror anchorVector first) =
      Coordinates3.Vector.scale first.quadrance anchorVector := by
  have selfCross : Coordinates3.Vector.cross first first = Coordinates3.Vector.zero := by
    ext <;> unfold Coordinates3.Vector.cross Coordinates3.Vector.zero <;> ring1
  unfold Geometry.Rotations.Axis.Recovery.capSecondMirror
  rw [Coordinates3.Vector.cross_add_right, selfCross, Coordinates3.Vector.zero_add,
    Coordinates3.Vector.vector_triple_product]
  unfold Coordinates3.Vector.Perpendicular at perpendicular
  rw [perpendicular]
  ext <;> unfold Coordinates3.Vector.sub Coordinates3.Vector.scale Coordinates3.Vector.quadrance <;>
    ring1

/-- For a perpendicular first mirror, the second mirror quadrance is the first quadrance times the cap denominator. -/
theorem quadrance_capSecondMirror (anchorVector first : Coordinates3.Vector K)
    (perpendicular : first.Perpendicular anchorVector) :
    (Geometry.Rotations.Axis.Recovery.capSecondMirror anchorVector first).quadrance =
      first.quadrance * (1 + anchorVector.quadrance) := by
  have firstCrossDot :
      Coordinates3.Vector.dot first (Coordinates3.Vector.cross anchorVector first) = 0 := by
    rw [Coordinates3.Vector.dot_comm]
    exact Coordinates3.Vector.cross_dot_right anchorVector first
  have anchorFirstDot : Coordinates3.Vector.dot anchorVector first = 0 := by
    rw [Coordinates3.Vector.dot_comm]
    exact perpendicular
  have lagrange := Coordinates3.Vector.lagrange anchorVector first
  rw [anchorFirstDot] at lagrange
  have crossQuadrance :
      (Coordinates3.Vector.cross anchorVector first).quadrance =
        anchorVector.quadrance * first.quadrance := by
    calc
      (Coordinates3.Vector.cross anchorVector first).quadrance =
          0 ^ 2 + (Coordinates3.Vector.cross anchorVector first).quadrance := by ring1
      _ = anchorVector.quadrance * first.quadrance := lagrange
  unfold Geometry.Rotations.Axis.Recovery.capSecondMirror
  rw [Coordinates3.Vector.quadrance_add, firstCrossDot, crossQuadrance]
  ring1

/-- A defined cap and a non-null perpendicular first mirror give a non-null second mirror. -/
theorem capSecondMirror_nonNull (anchorVector first : Coordinates3.Vector K)
    (anchorDefined : Cap.capDenominator anchorVector ≠ 0)
    (firstNonNull : first.quadrance ≠ 0)
    (perpendicular : first.Perpendicular anchorVector) :
    (Geometry.Rotations.Axis.Recovery.capSecondMirror anchorVector first).quadrance ≠ 0 := by
  rw [Geometry.Rotations.Axis.Recovery.quadrance_capSecondMirror anchorVector first perpendicular]
  apply Algebra.Field.ExplicitField.mul_ne_zero firstNonNull
  unfold Cap.capDenominator at anchorDefined
  exact anchorDefined

/-- The first and constructed second mirrors recover the prescribed cap anchor. -/
private theorem reflectionProductAnchorVector_capSecondMirror
    (anchorVector first : Coordinates3.Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (perpendicular : first.Perpendicular anchorVector) :
    Geometry.Rotations.Axis.Recovery.reflectionProductAnchorVector first
      (Geometry.Rotations.Axis.Recovery.capSecondMirror anchorVector first)
        (by rw [Geometry.Rotations.Axis.Recovery.dot_capSecondMirror]; exact firstNonNull) =
      anchorVector := by
  have cancel : (1 / first.quadrance) * first.quadrance = (1 : K) :=
    Algebra.Field.ExplicitField.div_mul_cancel 1 firstNonNull
  unfold Geometry.Rotations.Axis.Recovery.reflectionProductAnchorVector
  rw [Geometry.Rotations.Axis.Recovery.dot_capSecondMirror,
    Geometry.Rotations.Axis.Recovery.cross_capSecondMirror anchorVector first perpendicular,
    Coordinates3.Vector.scale_scale, cancel, Coordinates3.Vector.one_scale]

/-- The non-half-turn branch of Theorem 40, with an arbitrary certified first mirror normal perpendicular to the anchor
vector. -/
theorem reflection_mul_capSecondMirror (anchorVector first : Coordinates3.Vector K)
    (anchorDefined : Cap.capDenominator anchorVector ≠ 0)
    (firstNonNull : first.quadrance ≠ 0)
    (perpendicular : first.Perpendicular anchorVector)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.mul (Reflection.reflection first firstNonNull)
        (Reflection.reflection (Geometry.Rotations.Axis.Recovery.capSecondMirror anchorVector first)
          (Geometry.Rotations.Axis.Recovery.capSecondMirror_nonNull anchorVector first anchorDefined
            firstNonNull perpendicular)) =
      Cap.cap anchorVector anchorDefined := by
  let second := Geometry.Rotations.Axis.Recovery.capSecondMirror anchorVector first
  let secondNonNull := Geometry.Rotations.Axis.Recovery.capSecondMirror_nonNull anchorVector first
    anchorDefined firstNonNull perpendicular
  let dotNonzero : Coordinates3.Vector.dot first second ≠ 0 := by
    unfold second
    rw [Geometry.Rotations.Axis.Recovery.dot_capSecondMirror]
    exact firstNonNull
  let product := Reflection.reflectionProductRotation first second firstNonNull
    secondNonNull
  let productNotHalfTurn := Geometry.Rotations.Axis.Recovery.reflectionProduct_notHalfTurn first second
    firstNonNull secondNonNull dotNonzero twoNonzero
  let productAnchorDefined := Geometry.Rotations.Axis.Recovery.rotationAnchorVector_capDefined product
    productNotHalfTurn twoNonzero
  have recoveredVector :
      Geometry.Rotations.Axis.Recovery.rotationAnchorVector product productNotHalfTurn = anchorVector := by
    calc
      Geometry.Rotations.Axis.Recovery.rotationAnchorVector product productNotHalfTurn =
          Geometry.Rotations.Axis.Recovery.reflectionProductAnchorVector first second dotNonzero := by
            unfold product productNotHalfTurn
            exact Geometry.Rotations.Axis.Recovery.rotationAnchorVector_reflectionProduct first second
              firstNonNull secondNonNull dotNonzero twoNonzero
      _ = anchorVector := by
        unfold second dotNonzero
        exact Geometry.Rotations.Axis.Recovery.reflectionProductAnchorVector_capSecondMirror
          anchorVector first
          firstNonNull perpendicular
  change product.matrix = Cap.cap anchorVector anchorDefined
  calc
    product.matrix =
        Cap.cap (Geometry.Rotations.Axis.Recovery.rotationAnchorVector product productNotHalfTurn)
          productAnchorDefined :=
      (Geometry.Rotations.Axis.Recovery.cap_rotationAnchor product productNotHalfTurn twoNonzero).symm
    _ = Cap.cap anchorVector anchorDefined := by
      unfold Cap.cap
      rw [recoveredVector]

/-- The free-first-mirror form of Theorem 40 for a rotation in the affine anchor chart. -/
theorem reflectionProduct_eq_rotation_of_notHalfTurn
    (rotation : Rotations.Basic.Rotation K) (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) (first : Coordinates3.Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (perpendicular :
      first.Perpendicular (Geometry.Rotations.Axis.Recovery.rotationAnchorVector rotation notHalfTurn)) :
    Matrix3.mul (Reflection.reflection first firstNonNull)
        (Reflection.reflection
          (Geometry.Rotations.Axis.Recovery.capSecondMirror (Geometry.Rotations.Axis.Recovery.rotationAnchorVector
            rotation notHalfTurn) first)
          (Geometry.Rotations.Axis.Recovery.capSecondMirror_nonNull
            (Geometry.Rotations.Axis.Recovery.rotationAnchorVector rotation notHalfTurn) first
            (Geometry.Rotations.Axis.Recovery.rotationAnchorVector_capDefined rotation notHalfTurn twoNonzero)
            firstNonNull perpendicular)) =
      rotation.matrix := by
  calc
    Matrix3.mul (Reflection.reflection first firstNonNull)
        (Reflection.reflection
          (Geometry.Rotations.Axis.Recovery.capSecondMirror (Geometry.Rotations.Axis.Recovery.rotationAnchorVector
            rotation notHalfTurn) first)
          (Geometry.Rotations.Axis.Recovery.capSecondMirror_nonNull
            (Geometry.Rotations.Axis.Recovery.rotationAnchorVector rotation notHalfTurn) first
            (Geometry.Rotations.Axis.Recovery.rotationAnchorVector_capDefined rotation notHalfTurn twoNonzero)
            firstNonNull perpendicular)) =
      Cap.cap (Geometry.Rotations.Axis.Recovery.rotationAnchorVector rotation notHalfTurn)
        (Geometry.Rotations.Axis.Recovery.rotationAnchorVector_capDefined rotation notHalfTurn twoNonzero) :=
          Geometry.Rotations.Axis.Recovery.reflection_mul_capSecondMirror
            (Geometry.Rotations.Axis.Recovery.rotationAnchorVector rotation notHalfTurn) first
            (Geometry.Rotations.Axis.Recovery.rotationAnchorVector_capDefined rotation notHalfTurn twoNonzero)
            firstNonNull perpendicular twoNonzero
    _ = rotation.matrix :=
      Geometry.Rotations.Axis.Recovery.cap_rotationAnchor rotation notHalfTurn twoNonzero

/-- The free-first-mirror form of Theorem 40 for the half-turn chart. -/
theorem reflectionProduct_eq_rotation_of_halfSpread_eq_one [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K) (halfTurnSpread : Spread.halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) (first : Coordinates3.Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (perpendicular :
      first.Perpendicular
        (Geometry.Rotations.Axis.Recovery.halfTurnAxis rotation halfTurnSpread twoNonzero)) :
    Matrix3.mul (Reflection.reflection first firstNonNull)
        (Reflection.reflection
          (Geometry.Rotations.Axis.Recovery.halfTurnSecondMirror
            (Geometry.Rotations.Axis.Recovery.halfTurnAxis rotation halfTurnSpread twoNonzero) first)
          (Geometry.Rotations.Axis.Recovery.halfTurnSecondMirror_nonNull
            (Geometry.Rotations.Axis.Recovery.halfTurnAxis rotation halfTurnSpread twoNonzero) first
            (Geometry.Rotations.Axis.Recovery.halfTurnAxis_nonNull rotation halfTurnSpread twoNonzero)
            firstNonNull perpendicular)) =
      rotation.matrix := by
  calc
    Matrix3.mul (Reflection.reflection first firstNonNull)
        (Reflection.reflection
          (Geometry.Rotations.Axis.Recovery.halfTurnSecondMirror
            (Geometry.Rotations.Axis.Recovery.halfTurnAxis rotation halfTurnSpread twoNonzero) first)
          (Geometry.Rotations.Axis.Recovery.halfTurnSecondMirror_nonNull
            (Geometry.Rotations.Axis.Recovery.halfTurnAxis rotation halfTurnSpread twoNonzero) first
            (Geometry.Rotations.Axis.Recovery.halfTurnAxis_nonNull rotation halfTurnSpread twoNonzero)
            firstNonNull perpendicular)) =
      Reflection.halfTurn (Geometry.Rotations.Axis.Recovery.halfTurnAxis rotation halfTurnSpread twoNonzero)
        (Geometry.Rotations.Axis.Recovery.halfTurnAxis_nonNull rotation halfTurnSpread twoNonzero) :=
          Geometry.Rotations.Axis.Recovery.reflection_mul_halfTurnSecondMirror
            (Geometry.Rotations.Axis.Recovery.halfTurnAxis rotation halfTurnSpread twoNonzero) first
            (Geometry.Rotations.Axis.Recovery.halfTurnAxis_nonNull rotation halfTurnSpread twoNonzero)
            firstNonNull perpendicular
    _ = rotation.matrix :=
      (Geometry.Rotations.Axis.Recovery.rotation_eq_halfTurn_halfTurnAxis rotation halfTurnSpread
        twoNonzero).symm

set_option genInjectivity false in
/-- Cached executable witnesses and certificates for a two-reflection factorization of a rotation. -/
structure ReflectionFactorization (rotation : Rotations.Basic.Rotation K) where
  /-- The first retained reflection normal. -/ first : Coordinates3.Vector K
  /-- The second retained reflection normal. -/ second : Coordinates3.Vector K
  /-- The first retained reflection normal has nonzero quadrance. -/ firstNonNull : first.quadrance ≠ 0
  /-- The second retained reflection normal has nonzero quadrance. -/ secondNonNull : second.quadrance ≠ 0
  /-- The row-order product of the two retained reflections is the original rotation matrix. -/ product_eq :
    Matrix3.mul (Reflection.reflection first firstNonNull)
      (Reflection.reflection second secondNonNull) = rotation.matrix

constructive_injectivity ReflectionFactorization

/-- Theorem 40: every rotation is constructively factored into two reflections. The canonical axis/spread witness
performs the sole chart test and perpendicular search; this construction consumes that cached data and stores both
mirror normals and their non-nullness certificates. -/
@[expose] public def twoReflectionsTheorem [DecidableEq K] (rotation : Rotations.Basic.Rotation K)
    (twoNonzero : (2 : K) ≠ 0) : Geometry.Rotations.Axis.Recovery.ReflectionFactorization rotation := by
  let witness := Geometry.Rotations.Axis.Recovery.rotationAxisSpreadWitness rotation twoNonzero
  cases witness.chart with
  | halfTurn halfTurnSpread axisNonNull matrixEq =>
    let second := Geometry.Rotations.Axis.Recovery.halfTurnSecondMirror witness.axis witness.direction
    let secondNonNull := Geometry.Rotations.Axis.Recovery.halfTurnSecondMirror_nonNull witness.axis
      witness.direction axisNonNull witness.directionNonNull
      witness.directionPerpendicular
    refine
      { first := witness.direction
        second := second
        firstNonNull := witness.directionNonNull
        secondNonNull := secondNonNull
        product_eq := ?_ }
    calc
      Matrix3.mul
          (Reflection.reflection witness.direction witness.directionNonNull)
          (Reflection.reflection second secondNonNull) =
        Reflection.halfTurn witness.axis axisNonNull := by
          unfold secondNonNull second
          exact Geometry.Rotations.Axis.Recovery.reflection_mul_halfTurnSecondMirror witness.axis
            witness.direction axisNonNull witness.directionNonNull
            witness.directionPerpendicular
      _ = rotation.matrix := matrixEq.symm
  | affine notHalfTurn defined matrixEq =>
    let second := Geometry.Rotations.Axis.Recovery.capSecondMirror witness.axis witness.direction
    let secondNonNull := Geometry.Rotations.Axis.Recovery.capSecondMirror_nonNull witness.axis witness.direction
      defined witness.directionNonNull witness.directionPerpendicular
    refine
      { first := witness.direction
        second := second
        firstNonNull := witness.directionNonNull
        secondNonNull := secondNonNull
        product_eq := ?_ }
    calc
      Matrix3.mul
          (Reflection.reflection witness.direction witness.directionNonNull)
          (Reflection.reflection second secondNonNull) =
        Cap.cap witness.axis defined := by
          unfold secondNonNull second
          exact Geometry.Rotations.Axis.Recovery.reflection_mul_capSecondMirror witness.axis witness.direction
            defined witness.directionNonNull witness.directionPerpendicular
            twoNonzero
      _ = rotation.matrix := matrixEq.symm

end Purelib.Geometry.Rotations.Axis.Recovery

end
