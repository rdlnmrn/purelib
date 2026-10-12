module

public import Purelib.Algebra.Quaternion.SplitMatrix
public import Purelib.Geometry.Rotations.Projective.Correspondence
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Finite.Odd.Presentation
import Purelib.Algebra.Quaternion.Projective.Basic
import Purelib.Geometry.Rotations.Basic
import Purelib.Geometry.Rotations.Projective.Action
import Purelib.LinearAlgebra.Coordinates2.Invertible

/-!
# Projective matrices for a split Euclidean quaternion algebra

A retained representation of negative one as two squares supplies the
matrix model. Every rotation has an executable invertible representative,
and the exact fibers are the original nonzero scalar matrix classes.
-/

public section

namespace Purelib.Geometry.Rotations.Projective.Matrix

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.Finite.Odd.Presentation (TwoSquareRepresentation)
open Purelib.Algebra.Quaternion
open Purelib.Algebra.Quaternion.Projective.Basic (NonNullProportion)
open Purelib.Geometry.Rotations
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2

variable {K : Type*} [ExplicitField K] (split : TwoSquareRepresentation (-1 : K))

/-- Decode an invertible matrix into the rotation of its original non-null split quaternion.

The supplied two-square certificate fixes the coordinate conversion. The
original decoded quaternion and its norm certificate are retained by the
rotation construction, without any projective normalization.
-/
@[expose] def rotation (twoNonzero : (2 : K) ≠ 0) (value : Matrix2.Invertible K) : Basic.Rotation K :=
  Action.NonNullProportion.rotation (SplitMatrix.fromInvertible split twoNonzero value)

/-- Compute an invertible matrix representative of a displayed Euclidean rotation.

The original executable quaternion preimage is computed first. Its split
matrix retains the same norm as determinant, using the supplied two-square
certificate for negative one.
-/
@[expose] def representative [DecidableEq K] (twoNonzero : (2 : K) ≠ 0)
    (value : Basic.Rotation K) : Matrix2.Invertible K :=
  SplitMatrix.toInvertible split (Correspondence.RotationProportion.ofRotation value twoNonzero)

/-- The computed invertible representative reconstructs the original Euclidean rotation. -/
theorem rotation_representative [DecidableEq K] (twoNonzero : (2 : K) ≠ 0) (value : Basic.Rotation K) :
    rotation split twoNonzero (representative split twoNonzero value) = value := by
  unfold rotation representative
  rw [SplitMatrix.fromInvertible_toInvertible]
  apply Basic.Rotation.eq_of_matrix_eq
  exact Correspondence.RotationProportion.ofRotation_rotationMatrix value twoNonzero

/-- Multiplying invertible matrices gives the ordered product of their original Euclidean rotations. -/
theorem rotation_mul (twoNonzero : (2 : K) ≠ 0) (left right : Matrix2.Invertible K) :
    rotation split twoNonzero (Matrix2.Invertible.mul left right) =
      Basic.Rotation.mul (rotation split twoNonzero left) (rotation split twoNonzero right) := by
  unfold rotation
  rw [SplitMatrix.fromInvertible_mul]
  apply Basic.Rotation.eq_of_matrix_eq
  exact Action.NonNullProportion.rotationMatrix_mul _ _

/-- Two invertible matrices represent the same Euclidean rotation exactly when they differ by a nonzero scalar.

The supplied split certificate and nonzero two identify the original
quaternion algebra with all two-by-two matrices. The original quaternion
fiber theorem and matrix conversion preserve the same scale witnesses.
-/
theorem rotation_eq_iff_equivalent [DecidableEq K] (twoNonzero : (2 : K) ≠ 0)
    (left right : Matrix2.Invertible K) :
    rotation split twoNonzero left = rotation split twoNonzero right ↔ left.Equivalent right := by
  have fibers := (Correspondence.NonNullProportion.rotationMatrix_eq_iff_equivalent
    (SplitMatrix.fromInvertible split twoNonzero left)
    (SplitMatrix.fromInvertible split twoNonzero right) twoNonzero).trans
      (SplitMatrix.fromInvertible_equivalent_iff split twoNonzero left right)
  constructor
  · intro equal
    exact fibers.mp (congrArg Basic.Rotation.matrix equal)
  · intro equivalent
    exact Basic.Rotation.eq_of_matrix_eq _ _ (fibers.mpr equivalent)

/-- Reconstructing a represented Euclidean rotation returns a matrix in its original projective class. -/
theorem representative_rotation [DecidableEq K] (twoNonzero : (2 : K) ≠ 0) (value : Matrix2.Invertible K) :
    (representative split twoNonzero (rotation split twoNonzero value)).Equivalent value :=
  (rotation_eq_iff_equivalent split twoNonzero _ _).mp (rotation_representative split twoNonzero _)

/-- The original norm-one quaternion image equals the determinant-one matrix image of the same split rotation action.

The retained splitting certificate converts each original quaternion norm
into its matrix determinant. Both directions use the original coordinate
inverse, so the determinant-one preimage acts as the supplied rotation itself.
-/
theorem unitPreimage_iff_determinant_one (twoNonzero : (2 : K) ≠ 0) (target : Basic.Rotation K) :
    (∃ value : NonNullProportion K,
      Action.NonNullProportion.rotation value = target ∧ value.toProportion.norm = 1) ↔
      ∃ matrix : Matrix2.Invertible K, rotation split twoNonzero matrix = target ∧ matrix.matrix.determinant = 1 := by
  constructor
  · rintro ⟨value, represents, normOne⟩
    refine ⟨SplitMatrix.toInvertible split value, ?_, ?_⟩
    · unfold rotation
      rw [SplitMatrix.fromInvertible_toInvertible]
      exact represents
    · change Matrix2.determinant (SplitMatrix.toMatrix split value.toProportion) = 1
      rw [SplitMatrix.determinant_toMatrix]
      exact normOne
  · rintro ⟨matrix, represents, determinantOne⟩
    refine ⟨SplitMatrix.fromInvertible split twoNonzero matrix, represents, ?_⟩
    calc
      _ = Matrix2.determinant
          (SplitMatrix.toMatrix split (SplitMatrix.fromInvertible split twoNonzero matrix).toProportion) :=
        (SplitMatrix.determinant_toMatrix split _).symm
      _ = matrix.matrix.determinant := congrArg Matrix2.determinant
        (SplitMatrix.toMatrix_fromMatrix split twoNonzero matrix.matrix)
      _ = 1 := determinantOne

end Purelib.Geometry.Rotations.Projective.Matrix
