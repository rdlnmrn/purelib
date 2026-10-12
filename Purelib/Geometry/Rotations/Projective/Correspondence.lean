module

import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.Inverse
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Geometry.Rotations.Axis.Recovery
import Purelib.Geometry.Rotations.Cayley.Charts
import Purelib.Geometry.Rotations.Spread

import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Quaternion.Projective.Basic
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector
public import Purelib.Geometry.Rotations.Projective.Action
import Purelib.LinearAlgebra.Coordinates3.Antisymmetric
import Purelib.Geometry.Rotations.Basic
import Purelib.Geometry.Rotations.Reflection
import Purelib.Geometry.Rotations.Cayley.Cap
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

public section

/-!
# Rational rotations, Theorem 58 and Corollary 60

The projective bijection is expressed without a quotient: every rotation gets
an executable non-null representative, and two representatives give the same
matrix exactly when an explicit nonzero scale relates them.
-/

namespace Purelib.Geometry.Rotations.Projective.Correspondence

open Purelib
open Purelib.Algebra.Quaternion
open Purelib.Algebra.Quaternion.Projective.Basic
open Purelib.Geometry
open Purelib.Geometry.Rotations
open Purelib.Geometry.Rotations.Axis
open Purelib.Geometry.Rotations.Axis.Recovery
open Purelib.Geometry.Rotations.Cayley
open Purelib.Geometry.Rotations.Projective.Action
open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3.Antisymmetric
open Purelib.Geometry.Rotations.Basic
open Purelib.Geometry.Rotations.Reflection
open Purelib.Geometry.Rotations.Cayley.Cap

open Purelib.LinearAlgebra.Coordinates3

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section RotationProportion

/-- The affine inverse branch of Theorem 58. -/
@[expose] public def RotationProportion.affine (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) : Projective.Basic.NonNullProportion K where
  scalar := 1
  vector := Recovery.rotationAnchorVector rotation notHalfTurn
  normNonzero := by
    simpa only [Proportion.norm, Cap.capDenominator, one_pow] using
      Recovery.rotationAnchorVector_capDefined rotation notHalfTurn twoNonzero

/-- The scalar-one representative computed from the recovered anchor has the original rotation matrix. -/
theorem RotationProportion.affine_rotationMatrix (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    (NonNullProportion.rotationMatrix (Geometry.Rotations.Projective.Correspondence.RotationProportion.affine rotation
      notHalfTurn twoNonzero)) =
      rotation.matrix := by
  let proportion := Geometry.Rotations.Projective.Correspondence.RotationProportion.affine rotation notHalfTurn
    twoNonzero
  have scalarValue : proportion.scalar = 1 := rfl
  have vectorValue :
      proportion.vector = Recovery.rotationAnchorVector rotation notHalfTurn := rfl
  have scalarNonzero : proportion.scalar ≠ 0 := by
    rw [scalarValue]
    exact Purelib.Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero twoNonzero
  calc
    (NonNullProportion.rotationMatrix proportion) =
        Cap.cap (Coordinates3.Vector.scale proportion.scalar⁻¹ proportion.vector)
          (Charts.reciprocalAnchorCapDefined proportion.scalar proportion.vector
            scalarNonzero proportion.normNonzero) :=
      NonNullProportion.rotationMatrix_eq_cap proportion scalarNonzero
    _ = Cap.cap (Recovery.rotationAnchorVector rotation notHalfTurn)
        (Recovery.rotationAnchorVector_capDefined rotation notHalfTurn twoNonzero) := by
      congr 1
      rw [scalarValue, vectorValue,
        Purelib.Algebra.Field.Inverse.inverse_one
          (Purelib.Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero
          twoNonzero), Coordinates3.Vector.one_scale]
    _ = rotation.matrix := Recovery.cap_rotationAnchor rotation notHalfTurn twoNonzero

/-- The vector `w` in the paper's unnormalized inverse `(1 + tr(ρ) : w)`. -/
@[expose] public def RotationProportion.affineHomogeneousVector (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1) : Coordinates3.Vector K :=
  Coordinates3.Vector.scale (1 + Matrix3.trace rotation.matrix)
    (Recovery.rotationAnchorVector rotation notHalfTurn)

/-- The affine inverse in exactly the homogeneous scale printed in Theorem 58. -/
@[expose] public def RotationProportion.affineHomogeneous (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) : Projective.Basic.NonNullProportion K :=
  NonNullProportion.scale (1 + Matrix3.trace rotation.matrix)
    (Recovery.rotationAnchorDenominator_ne_zero rotation notHalfTurn twoNonzero)
    (Geometry.Rotations.Projective.Correspondence.RotationProportion.affine rotation notHalfTurn twoNonzero)

/-- The homogeneous affine representative has scalar coordinate `1 + tr R`. -/
theorem RotationProportion.affineHomogeneous_scalar (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    (Projective.Correspondence.RotationProportion.affineHomogeneous rotation notHalfTurn twoNonzero).scalar =
      1 + Matrix3.trace rotation.matrix := by
  unfold Projective.Correspondence.RotationProportion.affineHomogeneous NonNullProportion.scale
    Projective.Correspondence.RotationProportion.affine Proportion.scale
  ring1

/-- The homogeneous affine representative retains its displayed scaled anchor vector. -/
theorem RotationProportion.affineHomogeneous_vector (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    (Geometry.Rotations.Projective.Correspondence.RotationProportion.affineHomogeneous rotation notHalfTurn
      twoNonzero).vector =
      Geometry.Rotations.Projective.Correspondence.RotationProportion.affineHomogeneousVector rotation notHalfTurn :=
        rfl

/-- The displayed inverse vector satisfies `A_w=ρ-ρᵀ=2ρ_as`. -/
theorem RotationProportion.anchor_affineHomogeneousVector (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Antisymmetric.anchor (Projective.Correspondence.RotationProportion.affineHomogeneousVector rotation notHalfTurn) =
      Matrix3.sub rotation.matrix (Matrix3.transpose rotation.matrix) := by
  have denominatorNonzero := Recovery.rotationAnchorDenominator_ne_zero rotation
    notHalfTurn twoNonzero
  have cancel := Algebra.Field.ExplicitField.mul_inv_cancel
    (1 + Matrix3.trace rotation.matrix) denominatorNonzero
  unfold Projective.Correspondence.RotationProportion.affineHomogeneousVector
  rw [Antisymmetric.anchor_scale,
    Recovery.anchor_rotationAnchorVector rotation notHalfTurn twoNonzero]
  unfold Recovery.rotationAnchor
  rw [Matrix3.scale_scale]
  have coefficient :
      (1 + Matrix3.trace rotation.matrix) *
          (1 / (1 + Matrix3.trace rotation.matrix)) = 1 := by
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv, one_mul]
    exact cancel
  rw [coefficient, Matrix3.one_scale]

/-- Twice the antisymmetric part of a matrix equals the matrix minus its transpose when two is nonzero. -/
theorem RotationProportion.two_mul_antisymmetricPart (matrix : Coordinates3.Matrix3 K)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.scale 2 (Antisymmetric.antisymmetricPart matrix) =
      Matrix3.sub matrix (Matrix3.transpose matrix) := by
  have cancel := Algebra.Field.ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  unfold Antisymmetric.antisymmetricPart
  rw [Matrix3.scale_scale]
  have coefficient : (2 : K) * (1 / 2) = 1 := by
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv, one_mul]
    exact cancel
  rw [coefficient, Matrix3.one_scale]

/-- The homogeneous affine vector encodes twice the antisymmetric part of its rotation. -/
theorem RotationProportion.anchor_affineHomogeneousVector_eq_two_antisymmetricPart
    (rotation : Rotations.Basic.Rotation K) (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Antisymmetric.anchor (Geometry.Rotations.Projective.Correspondence.RotationProportion.affineHomogeneousVector
      rotation notHalfTurn) =
      Matrix3.scale 2 (Antisymmetric.antisymmetricPart rotation.matrix) := by
  rw [Geometry.Rotations.Projective.Correspondence.RotationProportion.anchor_affineHomogeneousVector rotation
    notHalfTurn twoNonzero,
    Geometry.Rotations.Projective.Correspondence.RotationProportion.two_mul_antisymmetricPart rotation.matrix
      twoNonzero]

/-- The homogeneous affine representative gives the original rotation matrix. -/
theorem RotationProportion.affineHomogeneous_rotationMatrix (rotation : Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    (NonNullProportion.rotationMatrix (Projective.Correspondence.RotationProportion.affineHomogeneous rotation
      notHalfTurn twoNonzero)) =
      rotation.matrix := by
  unfold Projective.Correspondence.RotationProportion.affineHomogeneous
  rw [NonNullProportion.rotationMatrix_scale,
    Geometry.Rotations.Projective.Correspondence.RotationProportion.affine_rotationMatrix rotation notHalfTurn
      twoNonzero]

/-- The infinity inverse branch of Theorem 58, using the executable row-pivot axis selected in the constructive
half-turn classification. -/
@[expose] public def RotationProportion.atInfinity [DecidableEq K] (rotation : Rotations.Basic.Rotation K)
    (halfTurnSpread : Spread.halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) : Projective.Basic.NonNullProportion K where
  scalar := 0
  vector := Recovery.halfTurnAxis rotation halfTurnSpread twoNonzero
  normNonzero := by
    unfold Purelib.Algebra.Quaternion.Projective.Basic.Proportion.norm
    rw [show (0 : K) ^ 2 = 0 by ring1, zero_add]
    exact Recovery.halfTurnAxis_nonNull rotation halfTurnSpread twoNonzero

/-- The scalar-zero representative of a half-spread-one rotation gives the original matrix. -/
theorem RotationProportion.atInfinity_rotationMatrix [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K) (halfTurnSpread : Spread.halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    (NonNullProportion.rotationMatrix (Geometry.Rotations.Projective.Correspondence.RotationProportion.atInfinity
      rotation halfTurnSpread twoNonzero)) =
      rotation.matrix := by
  rw [NonNullProportion.rotationMatrix_eq_halfTurn
    (Geometry.Rotations.Projective.Correspondence.RotationProportion.atInfinity rotation halfTurnSpread twoNonzero) (by
      rfl)]
  exact (Recovery.rotation_eq_halfTurn_halfTurnAxis rotation halfTurnSpread
    twoNonzero).symm

/-- Every nonzero image of `I + R` is a non-null axis when the rotation is a half turn.

The original half-turn projector is retained. Its image is non-null whenever
nonzero, and multiplying that image by two gives the specified image of
`I + R`. Coordinate basis inputs give each of its three rows.
-/
theorem RotationProportion.halfTurn_image_nonNull [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K) (halfTurnSpread : Spread.halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) (vector : Coordinates3.Vector K)
    (nonzero : Matrix3.rowMul vector (Matrix3.add Matrix3.identity rotation.matrix) ≠ Coordinates3.Vector.zero) :
    (Matrix3.rowMul vector (Matrix3.add Matrix3.identity rotation.matrix)).quadrance ≠ 0 := by
  let witness := Recovery.halfTurnAxisWitness rotation halfTurnSpread twoNonzero
  have doubled : Coordinates3.Vector.scale 2 (Matrix3.rowMul vector (Recovery.halfTurnProjector rotation)) =
      Matrix3.rowMul vector (Matrix3.add Matrix3.identity rotation.matrix) := by
    calc
      _ = Matrix3.rowMul vector (Matrix3.scale 2 (Recovery.halfTurnProjector rotation)) :=
        (Matrix3.rowMul_scale vector 2 _).symm
      _ = _ := congrArg (Matrix3.rowMul vector) (Recovery.halfTurnProjector_doubled rotation twoNonzero)
  have projectedNonzero : Matrix3.rowMul vector (Recovery.halfTurnProjector rotation) ≠
      Coordinates3.Vector.zero := by
    intro zero
    apply nonzero
    calc
      _ = Coordinates3.Vector.scale 2 (Matrix3.rowMul vector (Recovery.halfTurnProjector rotation)) :=
        doubled.symm
      _ = Coordinates3.Vector.zero := by rw [zero, Coordinates3.Vector.scale_zero]
  have projectedNonNull := witness.image_nonNull vector projectedNonzero
  exact doubled ▸ Coordinates3.Vector.quadrance_scale_ne_zero 2 _ twoNonzero projectedNonNull

/-- Any nonzero image of `I + R` gives the pure quaternion representative of a half turn.

The input vector chooses the image, without replacing the original retained
half-turn axis. The normalized projector readback proves that this image has
the same axis line, so its original projective rotation is exactly `R`.
-/
theorem RotationProportion.halfTurn_image_rotationMatrix [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K) (halfTurnSpread : Spread.halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) (vector : Coordinates3.Vector K)
    (nonzero : Matrix3.rowMul vector (Matrix3.add Matrix3.identity rotation.matrix) ≠ Coordinates3.Vector.zero) :
    NonNullProportion.rotationMatrix
      (Projective.Basic.NonNullProportion.ofNonNullVector
        (Matrix3.rowMul vector (Matrix3.add Matrix3.identity rotation.matrix))
        (RotationProportion.halfTurn_image_nonNull rotation halfTurnSpread twoNonzero vector nonzero)) =
      rotation.matrix := by
  let witness := Recovery.halfTurnAxisWitness rotation halfTurnSpread twoNonzero
  let image := Matrix3.rowMul vector (Matrix3.add Matrix3.identity rotation.matrix)
  let factor := 2 * (1 / witness.vector.quadrance) * vector.dot witness.vector
  have imageEq : image = Coordinates3.Vector.scale factor witness.vector := by
    calc
      image = Matrix3.rowMul vector (Matrix3.scale 2 (Recovery.halfTurnProjector rotation)) :=
        congrArg (Matrix3.rowMul vector) (Recovery.halfTurnProjector_doubled rotation twoNonzero).symm
      _ = Matrix3.rowMul vector (Matrix3.scale 2
          (Matrix3.scale (1 / witness.vector.quadrance) (Matrix3.outer witness.vector witness.vector))) :=
        congrArg (fun matrix => Matrix3.rowMul vector (Matrix3.scale 2 matrix)) witness.reconstruction
      _ = Coordinates3.Vector.scale factor witness.vector := by
        rw [Matrix3.scale_scale, Matrix3.rowMul_scale, Matrix3.rowMul_outer, Coordinates3.Vector.scale_scale]
  have factorNonzero : factor ≠ 0 := by
    intro zero
    apply nonzero
    change image = Coordinates3.Vector.zero
    rw [imageEq, zero, Coordinates3.Vector.zero_scale]
  rw [NonNullProportion.rotationMatrix_eq_halfTurn _ (by rfl)]
  change Reflection.halfTurn image _ = rotation.matrix
  have scaled : Reflection.halfTurn image
      (RotationProportion.halfTurn_image_nonNull rotation halfTurnSpread twoNonzero vector nonzero) =
      Reflection.halfTurn witness.vector witness.nonNull := by
    have transport := congrArg (fun axis : Coordinates3.Vector K =>
      Matrix3.neg (Matrix3.sub Matrix3.identity
        (Matrix3.scale (2 / axis.quadrance) (Matrix3.outer axis axis)))) imageEq
    change Reflection.halfTurn image
        (RotationProportion.halfTurn_image_nonNull rotation halfTurnSpread twoNonzero vector nonzero) =
      Reflection.halfTurn (Coordinates3.Vector.scale factor witness.vector)
        (Coordinates3.Vector.quadrance_scale_ne_zero factor witness.vector factorNonzero witness.nonNull) at transport
    exact transport.trans (Reflection.halfTurn_scale factor witness.vector factorNonzero witness.nonNull)
  exact scaled.trans (Recovery.rotation_eq_halfTurn_halfTurnAxis rotation halfTurnSpread twoNonzero).symm

/-- Construct a non-null quaternion proportion from the retained affine or half-turn axis chart.

The scalar is respectively one or zero, and the original chart supplies the norm certificate. -/
private def
  RotationProportion.ofAxisChart
  (rotation : Rotations.Basic.Rotation K) (axis : Coordinates3.Vector K)
    (chart : Recovery.RotationAxisChart rotation axis) : Projective.Basic.NonNullProportion K :=
  match chart with
  | .affine _ defined _ =>
      { scalar := 1
        vector := axis
        normNonzero := by
          simpa only [Purelib.Algebra.Quaternion.Projective.Basic.Proportion.norm, Cap.capDenominator, one_pow] using
            defined }
  | .halfTurn _ axisNonNull _ =>
      { scalar := 0
        vector := axis
        normNonzero := by
          unfold Purelib.Algebra.Quaternion.Projective.Basic.Proportion.norm
          rw [show (0 : K) ^ 2 = 0 by ring1, zero_add]
          exact axisNonNull }

/-- The quaternion proportion built from an axis chart gives the original rotation matrix. -/
private theorem
  RotationProportion.ofAxisChart_rotationMatrix
  (rotation : Rotations.Basic.Rotation K)
    (axis : Coordinates3.Vector K) (chart : Recovery.RotationAxisChart rotation axis)
    (twoNonzero : (2 : K) ≠ 0) :
    (NonNullProportion.rotationMatrix
      (Geometry.Rotations.Projective.Correspondence.RotationProportion.ofAxisChart rotation
      axis chart)) = rotation.matrix := by
  cases chart with
  | affine notHalfTurn defined matrixEq =>
      let proportion :=
        Geometry.Rotations.Projective.Correspondence.RotationProportion.ofAxisChart rotation
        axis
        (RotationAxisChart.affine notHalfTurn defined matrixEq)
      have scalarNonzero : proportion.scalar ≠ 0 := by
        change (1 : K) ≠ 0
        exact Purelib.Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero
          twoNonzero
      calc
        (NonNullProportion.rotationMatrix proportion) =
            Cap.cap (Coordinates3.Vector.scale proportion.scalar⁻¹ proportion.vector)
              (Charts.reciprocalAnchorCapDefined proportion.scalar
                proportion.vector scalarNonzero proportion.normNonzero) :=
          NonNullProportion.rotationMatrix_eq_cap proportion scalarNonzero
        _ = Cap.cap axis defined := by
          congr 1
          change Coordinates3.Vector.scale (1 : K)⁻¹ axis = axis
          rw [Purelib.Algebra.Field.Inverse.inverse_one
            (Purelib.Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero
            twoNonzero),
            Coordinates3.Vector.one_scale]
        _ = rotation.matrix := matrixEq.symm
  | halfTurn halfTurnSpread axisNonNull matrixEq =>
      let proportion :=
        Geometry.Rotations.Projective.Correspondence.RotationProportion.ofAxisChart rotation
        axis
        (RotationAxisChart.halfTurn halfTurnSpread axisNonNull matrixEq)
      calc
        (NonNullProportion.rotationMatrix proportion) = Reflection.halfTurn axis axisNonNull := by
          exact NonNullProportion.rotationMatrix_eq_halfTurn proportion rfl
        _ = rotation.matrix := matrixEq.symm

/-- The executable inverse representative from Theorem 58. It consumes the canonical axis wrapper, so the
affine/infinity chart decision and axis extraction are shared with the spread and reflection-factorization APIs. -/
@[expose] public def RotationProportion.ofRotation [DecidableEq K] (rotation : Rotations.Basic.Rotation K)
    (twoNonzero : (2 : K) ≠ 0) : Projective.Basic.NonNullProportion K :=
  let witness := Recovery.rotationAxisSpreadWitness rotation twoNonzero
  match witness.chart with
  | .affine _ defined _ =>
      { scalar := 1
        vector := witness.axis
        normNonzero := by
          simpa only [Purelib.Algebra.Quaternion.Projective.Basic.Proportion.norm, Cap.capDenominator, one_pow] using
            defined }
  | .halfTurn _ axisNonNull _ =>
      { scalar := 0
        vector := witness.axis
        normNonzero := by
          unfold Purelib.Algebra.Quaternion.Projective.Basic.Proportion.norm
          rw [show (0 : K) ^ 2 = 0 by ring1, zero_add]
          exact axisNonNull }

/-- The executable representative selected for a rotation gives that rotation matrix. -/
theorem RotationProportion.ofRotation_rotationMatrix [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    (NonNullProportion.rotationMatrix (Geometry.Rotations.Projective.Correspondence.RotationProportion.ofRotation
      rotation twoNonzero)) = rotation.matrix :=
  by
    let witness := Recovery.rotationAxisSpreadWitness rotation twoNonzero
    have same : Geometry.Rotations.Projective.Correspondence.RotationProportion.ofRotation rotation twoNonzero =
        Geometry.Rotations.Projective.Correspondence.RotationProportion.ofAxisChart rotation
          witness.axis witness.chart := by
      dsimp [Geometry.Rotations.Projective.Correspondence.RotationProportion.ofRotation,
        Geometry.Rotations.Projective.Correspondence.RotationProportion.ofAxisChart, witness]
      cases (Recovery.rotationAxisSpreadWitness rotation twoNonzero).chart <;> rfl
    rw [same]
    exact
      Purelib.Geometry.Rotations.Projective.Correspondence.RotationProportion.ofAxisChart_rotationMatrix
      rotation witness.axis witness.chart twoNonzero

end RotationProportion

section NonNullProportion

/-- The fixed line of a half turn consists exactly of scalar multiples of its axis; the scalar witness is displayed
explicitly. -/
theorem NonNullProportion.vector_eq_scale_of_halfTurn_fixed (axis other : Coordinates3.Vector K)
    (axisNonNull : axis.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (fixed : Matrix3.rowMul other (Reflection.halfTurn axis axisNonNull) = other) :
    other = Coordinates3.Vector.scale (Coordinates3.Vector.dot other axis / axis.quadrance) axis := by
  have negReflected :
      Coordinates3.Vector.neg (Matrix3.rowMul other (Reflection.reflection axis axisNonNull)) =
        other := by
    simpa only [Reflection.halfTurn, Matrix3.rowMul_neg] using fixed
  have reflectedNeg :
      Matrix3.rowMul other (Reflection.reflection axis axisNonNull) =
        Coordinates3.Vector.neg other := by
    calc
      Matrix3.rowMul other (Reflection.reflection axis axisNonNull) =
          Coordinates3.Vector.neg
            (Coordinates3.Vector.neg
              (Matrix3.rowMul other (Reflection.reflection axis axisNonNull))) := by
        apply Coordinates3.Vector.ext <;> unfold Coordinates3.Vector.neg <;> ring1
      _ = Coordinates3.Vector.neg other := by rw [negReflected]
  rw [Reflection.rowMul_reflection] at reflectedNeg
  apply Coordinates3.Vector.ext
  · apply
      Purelib.Algebra.Field.Characteristic.Nonzero.eq_of_two_mul_eq_two_mul
      twoNonzero
    have coordinate := congrArg Coordinates3.Vector.t reflectedNeg
    calc
      2 * other.t =
          (other.t -
              (2 * Coordinates3.Vector.dot other axis / axis.quadrance) * axis.t) +
            other.t +
            (2 * Coordinates3.Vector.dot other axis / axis.quadrance) * axis.t := by ring1
      _ = -other.t + other.t +
          (2 * Coordinates3.Vector.dot other axis / axis.quadrance) * axis.t := by
        simpa only [Coordinates3.Vector.sub_t, Coordinates3.Vector.scale_t, Coordinates3.Vector.neg_t] using
          congrArg
            (fun value => value + other.t +
              (2 * Coordinates3.Vector.dot other axis / axis.quadrance) * axis.t)
            coordinate
      _ = 2 *
          (Coordinates3.Vector.dot other axis / axis.quadrance * axis.t) := by
        simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
        ring1
  · apply
      Purelib.Algebra.Field.Characteristic.Nonzero.eq_of_two_mul_eq_two_mul
      twoNonzero
    have coordinate := congrArg Coordinates3.Vector.r reflectedNeg
    calc
      2 * other.r =
          (other.r -
              (2 * Coordinates3.Vector.dot other axis / axis.quadrance) * axis.r) +
            other.r +
            (2 * Coordinates3.Vector.dot other axis / axis.quadrance) * axis.r := by ring1
      _ = -other.r + other.r +
          (2 * Coordinates3.Vector.dot other axis / axis.quadrance) * axis.r := by
        simpa only [Coordinates3.Vector.sub_r, Coordinates3.Vector.scale_r, Coordinates3.Vector.neg_r] using
          congrArg
            (fun value => value + other.r +
              (2 * Coordinates3.Vector.dot other axis / axis.quadrance) * axis.r)
            coordinate
      _ = 2 *
          (Coordinates3.Vector.dot other axis / axis.quadrance * axis.r) := by
        simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
        ring1
  · apply
      Purelib.Algebra.Field.Characteristic.Nonzero.eq_of_two_mul_eq_two_mul
      twoNonzero
    have coordinate := congrArg Coordinates3.Vector.s reflectedNeg
    calc
      2 * other.s =
          (other.s -
              (2 * Coordinates3.Vector.dot other axis / axis.quadrance) * axis.s) +
            other.s +
            (2 * Coordinates3.Vector.dot other axis / axis.quadrance) * axis.s := by ring1
      _ = -other.s + other.s +
          (2 * Coordinates3.Vector.dot other axis / axis.quadrance) * axis.s := by
        simpa only [Coordinates3.Vector.sub_s, Coordinates3.Vector.scale_s, Coordinates3.Vector.neg_s] using
          congrArg
            (fun value => value + other.s +
              (2 * Coordinates3.Vector.dot other axis / axis.quadrance) * axis.s)
            coordinate
      _ = 2 *
          (Coordinates3.Vector.dot other axis / axis.quadrance * axis.s) := by
        simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
        ring1

/-- Equality of two half turns forces equality of their represented projective axis lines. -/
theorem NonNullProportion.vector_scale_of_halfTurn_eq (left right : Coordinates3.Vector K)
    (leftNonNull : left.quadrance ≠ 0)
    (rightNonNull : right.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (equal : Reflection.halfTurn left leftNonNull = Reflection.halfTurn right rightNonNull) :
    ∃ factor : K, factor ≠ 0 ∧ right = Coordinates3.Vector.scale factor left := by
  let factor := Coordinates3.Vector.dot right left / left.quadrance
  have rightFixed : Matrix3.rowMul right (Reflection.halfTurn left leftNonNull) = right := by
    rw [equal, Reflection.rowMul_self_halfTurn]
  have rightValue : right = Coordinates3.Vector.scale factor left :=
    Geometry.Rotations.Projective.Correspondence.NonNullProportion.vector_eq_scale_of_halfTurn_fixed left right
      leftNonNull twoNonzero
      rightFixed
  have factorNonzero : factor ≠ 0 := by
    intro factorZero
    apply rightNonNull
    rw [rightValue, Coordinates3.Vector.quadrance_scale, factorZero]
    ring1
  exact ⟨factor, factorNonzero, rightValue⟩

open Purelib.Geometry.Rotations.Projective.Action.NonNullProportion in
/-- Equal represented rotation matrices have equal half spread. -/
private theorem
  NonNullProportion.halfSpread_eq_of_rotationMatrix_eq
    {left right : Projective.Basic.NonNullProportion K}
    (equal : (NonNullProportion.rotationMatrix left) = (NonNullProportion.rotationMatrix right)) :
    Spread.halfSpread (NonNullProportion.rotation left) = Spread.halfSpread (NonNullProportion.rotation right) := by
  unfold Spread.halfSpread rotation
  exact congrArg (fun matrix => (3 - Matrix3.trace matrix) / 4) equal

/-- Equal rotation matrices from scalar-nonzero representatives determine an explicit nonzero projective scale. -/
private theorem
  NonNullProportion.affineEquivalent_of_rotationMatrix_eq
    (left right : Projective.Basic.NonNullProportion K)
    (leftScalarNonzero : left.scalar ≠ 0)
    (rightScalarNonzero : right.scalar ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (equal : (NonNullProportion.rotationMatrix left) = (NonNullProportion.rotationMatrix right)) :
    left.Equivalent right := by
  have capEqual := equal
  rw [NonNullProportion.rotationMatrix_eq_cap left leftScalarNonzero,
    NonNullProportion.rotationMatrix_eq_cap right rightScalarNonzero] at capEqual
  have normalizedEqual :
      Coordinates3.Vector.scale left.scalar⁻¹ left.vector =
        Coordinates3.Vector.scale right.scalar⁻¹ right.vector :=
    Cap.cap_injective twoNonzero _ _ _ _ capEqual
  let factor := right.scalar * left.scalar⁻¹
  have factorNonzero : factor ≠ 0 :=
    Algebra.Field.ExplicitField.mul_ne_zero rightScalarNonzero
      (Algebra.Field.ExplicitField.inv_ne_zero leftScalarNonzero)
  have leftCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    left.scalar leftScalarNonzero
  have rightCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    right.scalar rightScalarNonzero
  have reverseLeftCancel : left.scalar⁻¹ * left.scalar = 1 := by
    calc
      left.scalar⁻¹ * left.scalar =
          left.scalar * left.scalar⁻¹ := by ring1
      _ = 1 := leftCancel
  have reverseRightCancel : right.scalar⁻¹ * right.scalar = 1 := by
    calc
      right.scalar⁻¹ * right.scalar =
          right.scalar * right.scalar⁻¹ := by ring1
      _ = 1 := rightCancel
  refine ⟨factor, factorNonzero, ?_⟩
  apply Proportion.ext
  · unfold factor Proportion.scale
    calc
      right.scalar = right.scalar * 1 := by ring1
      _ = right.scalar * (left.scalar⁻¹ * left.scalar) := by
        rw [reverseLeftCancel]
      _ = (right.scalar * left.scalar⁻¹) * left.scalar := by ring1
  · apply Coordinates3.Vector.ext
    · have coordinate := congrArg Coordinates3.Vector.t normalizedEqual
      simp only [Coordinates3.Vector.scale_t] at coordinate
      unfold factor Proportion.scale Coordinates3.Vector.scale
      calc
        right.vector.t =
            (right.scalar * right.scalar⁻¹) * right.vector.t := by
          rw [rightCancel, one_mul]
        _ = right.scalar *
            (right.scalar⁻¹ * right.vector.t) := by ring1
        _ = right.scalar *
            (left.scalar⁻¹ * left.vector.t) := by
          rw [← coordinate]
        _ = (right.scalar * left.scalar⁻¹) * left.vector.t := by ring1
    · have coordinate := congrArg Coordinates3.Vector.r normalizedEqual
      simp only [Coordinates3.Vector.scale_r] at coordinate
      unfold factor Proportion.scale Coordinates3.Vector.scale
      calc
        right.vector.r =
            (right.scalar * right.scalar⁻¹) * right.vector.r := by
          rw [rightCancel, one_mul]
        _ = right.scalar *
            (right.scalar⁻¹ * right.vector.r) := by ring1
        _ = right.scalar *
            (left.scalar⁻¹ * left.vector.r) := by
          rw [← coordinate]
        _ = (right.scalar * left.scalar⁻¹) * left.vector.r := by ring1
    · have coordinate := congrArg Coordinates3.Vector.s normalizedEqual
      simp only [Coordinates3.Vector.scale_s] at coordinate
      unfold factor Proportion.scale Coordinates3.Vector.scale
      calc
        right.vector.s =
            (right.scalar * right.scalar⁻¹) * right.vector.s := by
          rw [rightCancel, one_mul]
        _ = right.scalar *
            (right.scalar⁻¹ * right.vector.s) := by ring1
        _ = right.scalar *
            (left.scalar⁻¹ * left.vector.s) := by
          rw [← coordinate]
        _ = (right.scalar * left.scalar⁻¹) * left.vector.s := by ring1

open Purelib.Geometry.Rotations.Projective.Correspondence.NonNullProportion in
/-- Equal rotation matrices from scalar-zero representatives determine an explicit nonzero projective scale. -/
private theorem
  NonNullProportion.infinityEquivalent_of_rotationMatrix_eq
    (left right : Projective.Basic.NonNullProportion K)
    (leftScalarZero : left.scalar = 0)
    (rightScalarZero : right.scalar = 0)
    (twoNonzero : (2 : K) ≠ 0)
    (equal : (NonNullProportion.rotationMatrix left) = (NonNullProportion.rotationMatrix right)) :
    left.Equivalent right := by
  have halfTurnsEqual := equal
  rw [NonNullProportion.rotationMatrix_eq_halfTurn left leftScalarZero,
    NonNullProportion.rotationMatrix_eq_halfTurn right rightScalarZero] at halfTurnsEqual
  rcases vector_scale_of_halfTurn_eq left.vector right.vector
      (NonNullProportion.vector_nonNull_of_scalar_eq_zero left leftScalarZero)
      (NonNullProportion.vector_nonNull_of_scalar_eq_zero right rightScalarZero)
      twoNonzero halfTurnsEqual with ⟨factor, factorNonzero, vectorValue⟩
  refine ⟨factor, factorNonzero, ?_⟩
  apply Proportion.ext
  · unfold Proportion.scale
    rw [leftScalarZero, rightScalarZero]
    ring1
  · exact vectorValue

/-- Injectivity in Theorem 58, stated exactly at representative level: equal rotation matrices are equivalent by a
displayed nonzero scale. -/
theorem NonNullProportion.equivalent_of_rotationMatrix_eq [DecidableEq K]
    (left right : Projective.Basic.NonNullProportion K) (twoNonzero : (2 : K) ≠ 0)
    (equal : (NonNullProportion.rotationMatrix left) = (NonNullProportion.rotationMatrix right)) :
    left.Equivalent right := by
  have spreadEqual :=
    Purelib.Geometry.Rotations.Projective.Correspondence.NonNullProportion.halfSpread_eq_of_rotationMatrix_eq
    equal
  by_cases leftScalarZero : left.scalar = 0
  · have leftSpreadOne : Spread.halfSpread (NonNullProportion.rotation left) = 1 :=
      (NonNullProportion.halfSpread_rotation_eq_one_iff left twoNonzero).2 leftScalarZero
    have rightSpreadOne : Spread.halfSpread (NonNullProportion.rotation right) = 1 := by
      rw [← spreadEqual]
      exact leftSpreadOne
    have rightScalarZero :=
      (NonNullProportion.halfSpread_rotation_eq_one_iff right twoNonzero).1 rightSpreadOne
    exact
      Purelib.Geometry.Rotations.Projective.Correspondence.NonNullProportion.infinityEquivalent_of_rotationMatrix_eq
      left right leftScalarZero
      rightScalarZero twoNonzero equal
  · have rightScalarNonzero : right.scalar ≠ 0 := by
      intro rightScalarZero
      have rightSpreadOne : Spread.halfSpread (NonNullProportion.rotation right) = 1 :=
        (NonNullProportion.halfSpread_rotation_eq_one_iff right twoNonzero).2 rightScalarZero
      have leftSpreadOne : Spread.halfSpread (NonNullProportion.rotation left) = 1 := by
        rw [spreadEqual]
        exact rightSpreadOne
      exact leftScalarZero
        ((NonNullProportion.halfSpread_rotation_eq_one_iff left twoNonzero).1 leftSpreadOne)
    exact
      Purelib.Geometry.Rotations.Projective.Correspondence.NonNullProportion.affineEquivalent_of_rotationMatrix_eq
      left right leftScalarZero
      rightScalarNonzero twoNonzero equal

/-- The injective half of Theorem 58 as an iff, paired with scale invariance. -/
theorem NonNullProportion.rotationMatrix_eq_iff_equivalent [DecidableEq K]
    (left right : Projective.Basic.NonNullProportion K) (twoNonzero : (2 : K) ≠ 0) :
    (NonNullProportion.rotationMatrix left) = (NonNullProportion.rotationMatrix right) ↔ left.Equivalent right := by
  constructor
  · exact Geometry.Rotations.Projective.Correspondence.NonNullProportion.equivalent_of_rotationMatrix_eq left right
      twoNonzero
  · intro equivalent
    exact NonNullProportion.rotationMatrix_respects_equivalent equivalent

/-- The exact kernel of the represented rotation consists of nonzero scalar quaternions.

The scale witness compares the original quaternion coordinates with the
original unit. No normalization or quotient replaces the retained input.
-/
theorem NonNullProportion.rotationMatrix_eq_identity_iff_scalar [DecidableEq K]
    (proportion : Projective.Basic.NonNullProportion K) (twoNonzero : (2 : K) ≠ 0) :
    NonNullProportion.rotationMatrix proportion = Matrix3.identity ↔
      ∃ factor : K, factor ≠ 0 ∧ proportion.toProportion = Proportion.scale factor Proportion.identity := by
  have equivalent := NonNullProportion.rotationMatrix_eq_iff_equivalent
    (Projective.Basic.NonNullProportion.identity proportion) proportion twoNonzero
  rw [NonNullProportion.rotationMatrix_identity] at equivalent
  constructor
  · intro identityMatrix
    exact equivalent.mp identityMatrix.symm
  · intro scalar
    exact (equivalent.mpr scalar).symm

end NonNullProportion

set_option genInjectivity false in
/-- The quotient-free group laws asserted by Corollary 60. Equality of projective points is
`NonNullProportion.Equivalent`; representative associativity and identity happen to hold as literal equalities. -/
structure ProjectiveProportionGroupLaws (K : Type*) [Algebra.Field.ExplicitField K]
    where
  /-- The retained non-null quaternion identity representative. -/ identity : Projective.Basic.NonNullProportion K
  /-- The retained inverse operation on non-null representatives. -/ inverse : Projective.Basic.NonNullProportion K →
    Projective.Basic.NonNullProportion K
  /-- Quaternion multiplication associates as a literal representative equality. -/ associative : ∀ (first second third
    : Projective.Basic.NonNullProportion K),
    NonNullProportion.mul (NonNullProportion.mul first second) third =
      NonNullProportion.mul first (NonNullProportion.mul second third)
  /-- The retained identity is a left unit as a literal representative equality. -/ leftIdentity : ∀ (proportion :
    Projective.Basic.NonNullProportion K),
    NonNullProportion.mul identity proportion = proportion
  /-- The retained identity is a right unit as a literal representative equality. -/ rightIdentity : ∀ (proportion :
    Projective.Basic.NonNullProportion K),
    NonNullProportion.mul proportion identity = proportion
  /-- The inverse times its representative is projectively equivalent to the retained identity. -/ leftInverse : ∀
    (proportion : Projective.Basic.NonNullProportion K),
    (NonNullProportion.mul (inverse proportion) proportion).Equivalent
      identity
  /-- The representative times its inverse is projectively equivalent to the retained identity. -/ rightInverse : ∀
    (proportion : Projective.Basic.NonNullProportion K),
    (NonNullProportion.mul proportion (inverse proportion)).Equivalent
      identity
  /-- Multiplication respects explicit projective scaling in both factors. -/ respectsEquivalent : ∀ {left left' right
    right' : Projective.Basic.NonNullProportion K},
    left.Equivalent left' → right.Equivalent right' →
      (NonNullProportion.mul left right).Equivalent
        (NonNullProportion.mul left' right')

constructive_injectivity ProjectiveProportionGroupLaws

/-- Corollary 60's projective group, with inverse given by quaternion conjugation. -/
@[expose] public def projectiveProportionGroupLaws (twoNonzero : (2 : K) ≠ 0) :
    Geometry.Rotations.Projective.Correspondence.ProjectiveProportionGroupLaws K := by
  let identity : Projective.Basic.NonNullProportion K :=
    { scalar := 1
      vector := Coordinates3.Vector.zero
      normNonzero := by
        unfold Purelib.Algebra.Quaternion.Projective.Basic.Proportion.norm
        rw [Coordinates3.Vector.quadrance_zero]
        simpa only [one_pow, add_zero] using
          Purelib.Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero twoNonzero
            }
  refine
    { identity := identity
      inverse := NonNullProportion.conjugate
      associative := NonNullProportion.mul_assoc
      leftIdentity := ?_
      rightIdentity := ?_
      leftInverse := ?_
      rightInverse := ?_
      respectsEquivalent := ?_ }
  · intro proportion
    apply NonNullProportion.ext (K := K)
    · exact congrArg Proportion.scalar
        (Proportion.identity_mul proportion.toProportion)
    · exact congrArg Proportion.vector
        (Proportion.identity_mul proportion.toProportion)
  · intro proportion
    apply NonNullProportion.ext (K := K)
    · exact congrArg Proportion.scalar
        (Proportion.mul_identity proportion.toProportion)
    · exact congrArg Proportion.vector
        (Proportion.mul_identity proportion.toProportion)
  · intro proportion
    apply NonNullProportion.equivalent_symm
    refine ⟨proportion.toProportion.norm, proportion.normNonzero, ?_⟩
    change Projective.Basic.Proportion.mul
        (Projective.Basic.Proportion.conjugate proportion.toProportion)
        proportion.toProportion =
      Proportion.scale proportion.toProportion.norm Projective.Basic.Proportion.identity
    exact Proportion.conjugate_mul proportion.toProportion
  · intro proportion
    apply NonNullProportion.equivalent_symm
    refine ⟨proportion.toProportion.norm, proportion.normNonzero, ?_⟩
    change Projective.Basic.Proportion.mul proportion.toProportion
        (Projective.Basic.Proportion.conjugate proportion.toProportion) =
      Proportion.scale proportion.toProportion.norm Projective.Basic.Proportion.identity
    exact Proportion.mul_conjugate proportion.toProportion
  · intro left left' right right' leftEquivalent rightEquivalent
    exact NonNullProportion.mul_respects_equivalent leftEquivalent
      rightEquivalent

set_option genInjectivity false in
/-- A quotient-free executable formulation of Theorem 58's bijection and multiplicativity. -/
structure ProjectiveRotationTheorem (K : Type*) [Algebra.Field.ExplicitField K]
    [DecidableEq K] where
  /-- Compute a non-null quaternion representative for each rotation. -/ representative : Rotations.Basic.Rotation K →
    Projective.Basic.NonNullProportion K
  /-- Each computed representative gives the original rotation matrix. -/ represents : ∀ rotation,
    (NonNullProportion.rotationMatrix (representative rotation)) = rotation.matrix
  /-- Equal represented rotation matrices admit an explicit nonzero projective scale. -/ injective : ∀ (left right :
    Projective.Basic.NonNullProportion K),
    (NonNullProportion.rotationMatrix left) = (NonNullProportion.rotationMatrix right) → left.Equivalent right
  /-- Quaternion multiplication gives the row-order product of represented rotation matrices. -/ multiplicative : ∀
    (left right : Projective.Basic.NonNullProportion K),
    (NonNullProportion.rotationMatrix (NonNullProportion.mul left right)) =
      Matrix3.mul (NonNullProportion.rotationMatrix left) (NonNullProportion.rotationMatrix right)

constructive_injectivity ProjectiveRotationTheorem

/-- Construct the correspondence between rotations and non-null projective quaternion proportions.

With decidable equality and nonzero two, compute a representative for every rotation and retain recovery, injectivity up
to projective equivalence, and multiplication laws (Theorem 58 and Corollary 60). -/
@[expose] public def projectiveRotationTheorem [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) : Geometry.Rotations.Projective.Correspondence.ProjectiveRotationTheorem K where
  representative := fun rotation =>
    Geometry.Rotations.Projective.Correspondence.RotationProportion.ofRotation rotation twoNonzero
  represents := fun rotation =>
    Geometry.Rotations.Projective.Correspondence.RotationProportion.ofRotation_rotationMatrix rotation twoNonzero
  injective := fun left right equal =>
    Geometry.Rotations.Projective.Correspondence.NonNullProportion.equivalent_of_rotationMatrix_eq left right twoNonzero
      equal
  multiplicative := NonNullProportion.rotationMatrix_mul

end Purelib.Geometry.Rotations.Projective.Correspondence
