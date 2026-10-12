module

public import Purelib.Algebra.Quaternion.Matrix
public import Purelib.Algebra.Field.Finite.Odd.Presentation
import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Coordinates2.Invertible
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring

/-!
# Split quaternion matrices from two retained square roots

A displayed solution of `a²+b²=-1` gives a complete two-by-two matrix
realization of the original quaternion algebra. An odd finite field's
original square-table scan computes precisely this certificate.
-/

public section

namespace Purelib.Algebra.Quaternion.SplitMatrix

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.Finite.Odd.Presentation (TwoSquareRepresentation FiniteOddFieldPresentation)
open Purelib.Algebra.Quaternion.Projective.Basic
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K]

/-- Encode an original quaternion using the two retained roots of negative one.

The spatial coordinates become `br-as` and `ar+bs`. Their squared sum
is the negative of the original spatial squared sum, so the determinant
is the original quaternion norm.
-/
@[expose] def toMatrix (split : TwoSquareRepresentation (-1 : K)) (value : Proportion K) : Matrix2 K :=
  ⟨value.scalar + split.first * value.vector.r + split.second * value.vector.s,
    -value.vector.t + split.second * value.vector.r - split.first * value.vector.s,
    value.vector.t + split.second * value.vector.r - split.first * value.vector.s,
    value.scalar - split.first * value.vector.r - split.second * value.vector.s⟩

/-- The split quaternion matrix determinant is exactly the original quaternion norm. -/
theorem determinant_toMatrix (split : TwoSquareRepresentation (-1 : K)) (value : Proportion K) :
    Matrix2.determinant (toMatrix split value) = Proportion.norm value := by
  calc
    _ = Proportion.norm value - (split.first ^ 2 + split.second ^ 2 + 1) *
        (value.vector.r ^ 2 + value.vector.s ^ 2) := by
      unfold Matrix2.determinant toMatrix Proportion.norm Vector3.quadrance Vector3.dot
      ring1
    _ = _ := by rw [split.equation]; ring1

/-- Conjugating the original quaternion takes the adjugate of its split matrix. -/
theorem toMatrix_conjugate (split : TwoSquareRepresentation (-1 : K)) (value : Proportion K) :
    toMatrix split (Proportion.conjugate value) = Matrix2.adjugate (toMatrix split value) := by
  ext <;> unfold toMatrix Proportion.conjugate Matrix2.adjugate Vector3.neg <;> ring1

/-- The split matrix realization preserves the original row-action quaternion multiplication. -/
theorem toMatrix_mul (split : TwoSquareRepresentation (-1 : K)) (left right : Proportion K) :
    toMatrix split (Proportion.mul left right) = Matrix2.mul (toMatrix split left) (toMatrix split right) := by
  apply Matrix2.ext
  · calc
      _ = (Matrix2.mul (toMatrix split left) (toMatrix split right)).a -
          (split.first ^ 2 + split.second ^ 2 + 1) *
            (left.vector.r * right.vector.r + left.vector.s * right.vector.s) := by
        unfold toMatrix Proportion.mul Vector3.dot Vector3.sub Vector3.add Vector3.scale Vector3.cross Matrix2.mul
        ring1
      _ = _ := by rw [split.equation]; ring1
  · calc
      _ = (Matrix2.mul (toMatrix split left) (toMatrix split right)).b +
          (split.first ^ 2 + split.second ^ 2 + 1) *
            (left.vector.r * right.vector.s - left.vector.s * right.vector.r) := by
        unfold toMatrix Proportion.mul Vector3.dot Vector3.sub Vector3.add Vector3.scale Vector3.cross Matrix2.mul
        ring1
      _ = _ := by rw [split.equation]; ring1
  · calc
      _ = (Matrix2.mul (toMatrix split left) (toMatrix split right)).c -
          (split.first ^ 2 + split.second ^ 2 + 1) *
            (left.vector.r * right.vector.s - left.vector.s * right.vector.r) := by
        unfold toMatrix Proportion.mul Vector3.dot Vector3.sub Vector3.add Vector3.scale Vector3.cross Matrix2.mul
        ring1
      _ = _ := by rw [split.equation]; ring1
  · calc
      _ = (Matrix2.mul (toMatrix split left) (toMatrix split right)).d -
          (split.first ^ 2 + split.second ^ 2 + 1) *
            (left.vector.r * right.vector.r + left.vector.s * right.vector.s) := by
        unfold toMatrix Proportion.mul Vector3.dot Vector3.sub Vector3.add Vector3.scale Vector3.cross Matrix2.mul
        ring1
      _ = _ := by rw [split.equation]; ring1

/-- Decode a matrix using the same two retained roots and the inverse of two.

The two spatial half-sums are multiplied by the negative of the original
root matrix, whose square is negative identity. No inverse root or
additional selected scalar is needed.
-/
@[expose] def fromMatrix (split : TwoSquareRepresentation (-1 : K)) (matrix : Matrix2 K) : Proportion K :=
  ⟨(2 : K)⁻¹ * (matrix.a + matrix.d),
    ⟨(2 : K)⁻¹ * (matrix.c - matrix.b),
      -(2 : K)⁻¹ * (split.first * (matrix.a - matrix.d) + split.second * (matrix.b + matrix.c)),
      (2 : K)⁻¹ * (split.first * (matrix.b + matrix.c) - split.second * (matrix.a - matrix.d))⟩⟩

/-- Decoding the split matrix recovers the original quaternion when two is nonzero. -/
theorem fromMatrix_toMatrix (split : TwoSquareRepresentation (-1 : K))
    (twoNonzero : (2 : K) ≠ 0) (value : Proportion K) : fromMatrix split (toMatrix split value) = value := by
  have cancelTwo := ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  apply Proportion.ext
  · calc
      _ = value.scalar * ((2 : K) * (2 : K)⁻¹) := by unfold fromMatrix toMatrix; ring1
      _ = _ := by rw [cancelTwo, mul_one]
  · apply Vector3.ext
    · calc
        _ = value.vector.t * ((2 : K) * (2 : K)⁻¹) := by unfold fromMatrix toMatrix; ring1
        _ = _ := by rw [cancelTwo, mul_one]
    · calc
        _ = -value.vector.r * ((2 : K) * (2 : K)⁻¹) * (split.first ^ 2 + split.second ^ 2) := by
          unfold fromMatrix toMatrix
          ring1
        _ = _ := by rw [cancelTwo, split.equation]; ring1
    · calc
        _ = -value.vector.s * ((2 : K) * (2 : K)⁻¹) * (split.first ^ 2 + split.second ^ 2) := by
          unfold fromMatrix toMatrix
          ring1
        _ = _ := by rw [cancelTwo, split.equation]; ring1

/-- Encoding decoded coordinates recovers every original matrix when two is nonzero. -/
theorem toMatrix_fromMatrix (split : TwoSquareRepresentation (-1 : K))
    (twoNonzero : (2 : K) ≠ 0) (matrix : Matrix2 K) : toMatrix split (fromMatrix split matrix) = matrix := by
  have cancelTwo := ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  apply Matrix2.ext
  · calc
      _ = (2 : K)⁻¹ * ((matrix.a + matrix.d) -
          (split.first ^ 2 + split.second ^ 2) * (matrix.a - matrix.d)) := by
        unfold toMatrix fromMatrix
        ring1
      _ = matrix.a * ((2 : K) * (2 : K)⁻¹) := by rw [split.equation]; ring1
      _ = _ := by rw [cancelTwo, mul_one]
  · calc
      _ = (2 : K)⁻¹ * (-(matrix.c - matrix.b) -
          (split.first ^ 2 + split.second ^ 2) * (matrix.b + matrix.c)) := by
        unfold toMatrix fromMatrix
        ring1
      _ = matrix.b * ((2 : K) * (2 : K)⁻¹) := by rw [split.equation]; ring1
      _ = _ := by rw [cancelTwo, mul_one]
  · calc
      _ = (2 : K)⁻¹ * ((matrix.c - matrix.b) -
          (split.first ^ 2 + split.second ^ 2) * (matrix.b + matrix.c)) := by
        unfold toMatrix fromMatrix
        ring1
      _ = matrix.c * ((2 : K) * (2 : K)⁻¹) := by rw [split.equation]; ring1
      _ = _ := by rw [cancelTwo, mul_one]
  · calc
      _ = (2 : K)⁻¹ * ((matrix.a + matrix.d) +
          (split.first ^ 2 + split.second ^ 2) * (matrix.a - matrix.d)) := by
        unfold toMatrix fromMatrix
        ring1
      _ = matrix.d * ((2 : K) * (2 : K)⁻¹) := by rw [split.equation]; ring1
      _ = _ := by rw [cancelTwo, mul_one]

/-- An odd finite field's original square-table scan computes a splitting certificate.

The retained roots and their equation are the original two-square
representation of negative one. All matrix operations consume that
same certificate, without repeating the scan.
-/
@[expose] def finiteSplit (presentation : FiniteOddFieldPresentation K) : TwoSquareRepresentation (-1 : K) :=
  presentation.twoSquareRepresentation (-1)

/-- The split matrix is the source Lorentz matrix of the same retained scalar and transformed spatial coordinates. -/
theorem toMatrix_eq_lorentz_coordinates (oneNonzero : (1 : K) ≠ 0)
    (split : TwoSquareRepresentation (-1 : K)) (value : Proportion K) :
    toMatrix split value = Clifford.Lorentz.Matrix.toMatrix oneNonzero
      (Clifford.Lorentz.Matrix.coordinates oneNonzero value.scalar
        ⟨value.vector.t, split.second * value.vector.r - split.first * value.vector.s,
          split.first * value.vector.r + split.second * value.vector.s⟩) := by
  rw [Clifford.Lorentz.Matrix.toMatrix_coordinates]
  ext <;> unfold toMatrix <;> ring1

/-- A supplied imaginary unit gives the original two-square splitting certificate. -/
@[expose] def imaginarySplit (i : K) (iSquare : i ^ 2 = -1) : TwoSquareRepresentation (-1 : K) :=
  ⟨0, i, by rw [zero_pow (by decide : 2 ≠ 0), zero_add, iSquare]⟩

/-- The imaginary-unit specialization is exactly the original quaternion matrix realization. -/
theorem toMatrix_imaginarySplit (i : K) (iSquare : i ^ 2 = -1) (value : Proportion K) :
    toMatrix (imaginarySplit i iSquare) value = Matrix.toMatrix i value := by
  ext <;> unfold toMatrix imaginarySplit Matrix.toMatrix <;> ring1

/-- The split quaternion matrix correspondence preserves homogeneous scaling of its original coordinates. -/
theorem toMatrix_scale (split : TwoSquareRepresentation (-1 : K)) (factor : K) (value : Proportion K) :
    toMatrix split (Proportion.scale factor value) = Matrix2.scalarScale factor (toMatrix split value) := by
  apply Matrix2.ext <;> unfold toMatrix Proportion.scale Vector3.scale Matrix2.scalarScale <;> ring1

/-- The matrix of an original non-null quaternion is invertible under the retained two-square splitting certificate. -/
@[expose] def toInvertible (split : TwoSquareRepresentation (-1 : K))
    (value : NonNullProportion K) : Matrix2.Invertible K where
  matrix := toMatrix split value.toProportion
  determinantNonzero := by rw [determinant_toMatrix]; exact value.normNonzero

/-- Decode an invertible split matrix into the original non-null quaternion owner.

The same retained pair of roots computes the original quaternion coordinates.
Two-sided matrix readback transports the supplied determinant certificate to
that exact decoded quaternion norm without selecting new splitting data.
-/
@[expose] def fromInvertible (split : TwoSquareRepresentation (-1 : K)) (twoNonzero : (2 : K) ≠ 0)
    (value : Matrix2.Invertible K) : NonNullProportion K :=
  let decoded := fromMatrix split value.matrix
  { toProportion := decoded
    normNonzero := by
      have norm : decoded.norm = value.matrix.determinant := by
        calc
          decoded.norm = (toMatrix split decoded).determinant := (determinant_toMatrix split decoded).symm
          _ = value.matrix.determinant := congrArg Matrix2.determinant
            (toMatrix_fromMatrix split twoNonzero value.matrix)
      rw [norm]
      exact value.determinantNonzero }

/-- Decoding the original non-null quaternion's split matrix returns that same quaternion record. -/
theorem fromInvertible_toInvertible (split : TwoSquareRepresentation (-1 : K)) (twoNonzero : (2 : K) ≠ 0)
    (value : NonNullProportion K) : fromInvertible split twoNonzero (toInvertible split value) = value := by
  have coordinates := fromMatrix_toMatrix split twoNonzero value.toProportion
  apply NonNullProportion.ext
  · exact congrArg Proportion.scalar coordinates
  · exact congrArg Proportion.vector coordinates

/-- Encoding the decoded non-null quaternion returns the original invertible matrix record. -/
theorem toInvertible_fromInvertible (split : TwoSquareRepresentation (-1 : K)) (twoNonzero : (2 : K) ≠ 0)
    (value : Matrix2.Invertible K) : toInvertible split (fromInvertible split twoNonzero value) = value :=
  Matrix2.Invertible.eq_of_matrix_eq (toMatrix_fromMatrix split twoNonzero value.matrix)

/-- The split correspondence preserves multiplication of the original non-null quaternion inputs. -/
theorem toInvertible_mul (split : TwoSquareRepresentation (-1 : K)) (left right : NonNullProportion K) :
    toInvertible split (NonNullProportion.mul left right) =
      Matrix2.Invertible.mul (toInvertible split left) (toInvertible split right) :=
  Matrix2.Invertible.eq_of_matrix_eq (toMatrix_mul split left.toProportion right.toProportion)

/-- Equality of split invertible matrices reflects equality of the two original non-null quaternions. -/
theorem toInvertible_injective (split : TwoSquareRepresentation (-1 : K)) (twoNonzero : (2 : K) ≠ 0)
    {left right : NonNullProportion K} (equal : toInvertible split left = toInvertible split right) : left = right := by
  calc
    left = fromInvertible split twoNonzero (toInvertible split left) :=
      (fromInvertible_toInvertible split twoNonzero left).symm
    _ = fromInvertible split twoNonzero (toInvertible split right) := congrArg (fromInvertible split twoNonzero) equal
    _ = right := fromInvertible_toInvertible split twoNonzero right

/-- Decoding invertible matrix multiplication preserves the original non-null quaternion product. -/
theorem fromInvertible_mul (split : TwoSquareRepresentation (-1 : K)) (twoNonzero : (2 : K) ≠ 0)
    (left right : Matrix2.Invertible K) :
    fromInvertible split twoNonzero (Matrix2.Invertible.mul left right) =
      NonNullProportion.mul (fromInvertible split twoNonzero left) (fromInvertible split twoNonzero right) := by
  apply toInvertible_injective split twoNonzero
  rw [toInvertible_fromInvertible, toInvertible_mul, toInvertible_fromInvertible, toInvertible_fromInvertible]

/-- The split correspondence preserves and reflects the exact nonzero projective scale of the original quaternions.

The same scalar relates both retained quaternion parents and their split
matrices. Matrix coordinate recovery reflects the scaled equality directly,
so neither input owner nor the relation witness is replaced.
-/
theorem toInvertible_equivalent_iff (split : TwoSquareRepresentation (-1 : K)) (twoNonzero : (2 : K) ≠ 0)
    (left right : NonNullProportion K) :
    (toInvertible split left).Equivalent (toInvertible split right) ↔ left.Equivalent right := by
  have injective {left right : Proportion K} (equal : toMatrix split left = toMatrix split right) : left = right := by
    calc
      left = fromMatrix split (toMatrix split left) := (fromMatrix_toMatrix split twoNonzero left).symm
      _ = fromMatrix split (toMatrix split right) := congrArg (fromMatrix split) equal
      _ = right := fromMatrix_toMatrix split twoNonzero right
  constructor
  · rintro ⟨factor, nonzero, represents⟩
    refine ⟨factor, nonzero, ?_⟩
    apply injective
    calc
      toMatrix split right.toProportion = Matrix2.scalarScale factor (toMatrix split left.toProportion) := represents
      _ = toMatrix split (Proportion.scale factor left.toProportion) :=
        (toMatrix_scale split factor left.toProportion).symm
  · rintro ⟨factor, nonzero, represents⟩
    refine ⟨factor, nonzero, ?_⟩
    calc
      toMatrix split right.toProportion = toMatrix split (Proportion.scale factor left.toProportion) :=
        congrArg (toMatrix split) represents
      _ = Matrix2.scalarScale factor (toMatrix split left.toProportion) := toMatrix_scale split factor left.toProportion

/-- Decoding preserves and reflects the original invertible matrices' projective scale relation. -/
theorem fromInvertible_equivalent_iff (split : TwoSquareRepresentation (-1 : K)) (twoNonzero : (2 : K) ≠ 0)
    (left right : Matrix2.Invertible K) :
    (fromInvertible split twoNonzero left).Equivalent (fromInvertible split twoNonzero right) ↔
      left.Equivalent right := by
  have correspondence := (toInvertible_equivalent_iff split twoNonzero
    (fromInvertible split twoNonzero left) (fromInvertible split twoNonzero right)).symm
  rw [toInvertible_fromInvertible, toInvertible_fromInvertible] at correspondence
  exact correspondence

end Purelib.Algebra.Quaternion.SplitMatrix
