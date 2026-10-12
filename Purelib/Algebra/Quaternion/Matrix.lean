module

public import Purelib.Algebra.Quaternion.Projective.Basic
public import Purelib.LinearAlgebra.Coordinates2.Matrix
public import Purelib.Algebra.Clifford.Lorentz.Matrix
public import Purelib.Algebra.Quadratic.Pair.ImaginaryField
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Algebra.Field.Inverse
import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Tactic.Ring

/-!
# Quaternion matrices with a displayed imaginary unit

The matrix model uses an explicitly supplied scalar whose square is negative
one. It applies within any admissible explicit field containing that scalar,
without constructing a completed complex field or choosing a square root.
-/

public section

namespace Purelib.Algebra.Quaternion.Matrix

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field (Embedding)
open Purelib.Algebra.Field.Characteristic.Nonzero (four_ne_zero)
open Purelib.Algebra
open Purelib.Algebra.Quaternion.Projective.Basic
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K]

/-- Encode a quaternion using the displayed imaginary unit in its matrix entries.

The row-action convention gives entries `x+is`, `-t+ir`, `t+ir`, `x-is`.
The square relation for the supplied unit is required by the algebraic laws.
-/
@[expose] def toMatrix (i : K) (value : Proportion K) : Matrix2 K :=
  ⟨value.scalar + i * value.vector.s, -value.vector.t + i * value.vector.r,
    value.vector.t + i * value.vector.r, value.scalar - i * value.vector.s⟩

namespace Pauli

/-- The first Pauli matrix exchanges the two coordinate directions. -/
@[expose] def first : Matrix2 K := ⟨0, 1, 1, 0⟩

/-- The second Pauli matrix has off-diagonal entries negative and positive imaginary unit. -/
@[expose] def second (i : K) : Matrix2 K := ⟨0, -i, i, 0⟩

/-- The third Pauli matrix has diagonal entries one and negative one. -/
@[expose] def third : Matrix2 K := ⟨1, 0, 0, -1⟩

end Pauli

/-- The quaternion matrix is the scalar identity plus the imaginary-unit Pauli combination.

The original row-action coordinates enter as `r`, negative `t`, and `s`.
The supplied square relation identifies the second Pauli contribution with
the original real off-diagonal entries.
-/
theorem toMatrix_eq_pauli (i : K) (iSquare : i ^ 2 = -1) (value : Proportion K) :
    toMatrix i value = Matrix2.add (Matrix2.scalarScale value.scalar Matrix2.identity)
      (Matrix2.scalarScale i (Matrix2.add
        (Matrix2.add (Matrix2.scalarScale value.vector.r Pauli.first)
          (Matrix2.scalarScale (-value.vector.t) (Pauli.second i)))
        (Matrix2.scalarScale value.vector.s Pauli.third))) := by
  apply Matrix2.ext
  · unfold toMatrix Matrix2.add Matrix2.scalarScale Matrix2.identity Pauli.first Pauli.second Pauli.third
    ring1
  · calc
      _ = (Matrix2.add (Matrix2.scalarScale value.scalar Matrix2.identity)
          (Matrix2.scalarScale i (Matrix2.add
            (Matrix2.add (Matrix2.scalarScale value.vector.r Pauli.first)
              (Matrix2.scalarScale (-value.vector.t) (Pauli.second i)))
            (Matrix2.scalarScale value.vector.s Pauli.third)))).b -
              (i ^ 2 + 1) * value.vector.t := by
        unfold toMatrix Matrix2.add Matrix2.scalarScale Matrix2.identity Pauli.first Pauli.second Pauli.third
        ring1
      _ = _ := by rw [iSquare]; ring1
  · calc
      _ = (Matrix2.add (Matrix2.scalarScale value.scalar Matrix2.identity)
          (Matrix2.scalarScale i (Matrix2.add
            (Matrix2.add (Matrix2.scalarScale value.vector.r Pauli.first)
              (Matrix2.scalarScale (-value.vector.t) (Pauli.second i)))
            (Matrix2.scalarScale value.vector.s Pauli.third)))).c +
              (i ^ 2 + 1) * value.vector.t := by
        unfold toMatrix Matrix2.add Matrix2.scalarScale Matrix2.identity Pauli.first Pauli.second Pauli.third
        ring1
      _ = _ := by rw [iSquare]; ring1
  · unfold toMatrix Matrix2.add Matrix2.scalarScale Matrix2.identity Pauli.first Pauli.second Pauli.third
    ring1

/-- The quaternion matrix is the Lorentz dihedron matrix with both spatial coordinates multiplied by its unit.

The displayed unit remains a parameter. The relation that its square is
negative one is needed by the quaternion norm and product laws, while
this literal matrix-coordinate dictionary holds for every supplied scalar.
-/
theorem toMatrix_eq_lorentz_coordinates (oneNonzero : (1 : K) ≠ 0) (i : K) (value : Proportion K) :
    toMatrix i value = Clifford.Lorentz.Matrix.toMatrix oneNonzero
      (Clifford.Lorentz.Matrix.coordinates oneNonzero value.scalar
        ⟨value.vector.t, i * value.vector.r, i * value.vector.s⟩) := by
  rw [Clifford.Lorentz.Matrix.toMatrix_coordinates]
  ext <;> unfold toMatrix <;> ring1

/-- The quaternion matrix determinant is its norm when the unit squares to negative one. -/
theorem determinant_toMatrix (i : K) (iSquare : i ^ 2 = -1) (value : Proportion K) :
    Matrix2.determinant (toMatrix i value) = Proportion.norm value := by
  calc
    Matrix2.determinant (toMatrix i value) = Proportion.norm value -
        (i ^ 2 + 1) * (value.vector.r ^ 2 + value.vector.s ^ 2) := by
      unfold Matrix2.determinant toMatrix Proportion.norm Vector3.quadrance Vector3.dot
      ring1
    _ = Proportion.norm value := by rw [iSquare]; ring1

/-- The sum of the diagonal entries is twice the scalar quaternion coordinate. -/
theorem diagonal_sum_toMatrix (i : K) (value : Proportion K) :
    (toMatrix i value).a + (toMatrix i value).d = 2 * value.scalar := by
  unfold toMatrix
  ring1

/-- Quaternion conjugation becomes matrix adjugation. -/
theorem toMatrix_conjugate (i : K) (value : Proportion K) :
    toMatrix i (Proportion.conjugate value) = Matrix2.adjugate (toMatrix i value) := by
  ext <;> unfold toMatrix Proportion.conjugate Matrix2.adjugate Vector3.neg <;> ring1

/-- The matrix model preserves the row-action quaternion product. -/
theorem toMatrix_mul (i : K) (iSquare : i ^ 2 = -1) (left right : Proportion K) :
    toMatrix i (Proportion.mul left right) = Matrix2.mul (toMatrix i left) (toMatrix i right) := by
  apply Matrix2.ext
  · calc
      (toMatrix i (Proportion.mul left right)).a =
          (Matrix2.mul (toMatrix i left) (toMatrix i right)).a -
            (i ^ 2 + 1) * (left.vector.r * right.vector.r + left.vector.s * right.vector.s) := by
        unfold toMatrix Proportion.mul Vector3.dot Vector3.sub Vector3.add Vector3.scale
          Vector3.cross Matrix2.mul
        ring1
      _ = (Matrix2.mul (toMatrix i left) (toMatrix i right)).a := by rw [iSquare]; ring1
  · calc
      (toMatrix i (Proportion.mul left right)).b =
          (Matrix2.mul (toMatrix i left) (toMatrix i right)).b -
            (i ^ 2 + 1) * (left.vector.s * right.vector.r - left.vector.r * right.vector.s) := by
        unfold toMatrix Proportion.mul Vector3.dot Vector3.sub Vector3.add Vector3.scale
          Vector3.cross Matrix2.mul
        ring1
      _ = (Matrix2.mul (toMatrix i left) (toMatrix i right)).b := by rw [iSquare]; ring1
  · calc
      (toMatrix i (Proportion.mul left right)).c =
          (Matrix2.mul (toMatrix i left) (toMatrix i right)).c -
            (i ^ 2 + 1) * (left.vector.r * right.vector.s - left.vector.s * right.vector.r) := by
        unfold toMatrix Proportion.mul Vector3.dot Vector3.sub Vector3.add Vector3.scale
          Vector3.cross Matrix2.mul
        ring1
      _ = (Matrix2.mul (toMatrix i left) (toMatrix i right)).c := by rw [iSquare]; ring1
  · calc
      (toMatrix i (Proportion.mul left right)).d =
          (Matrix2.mul (toMatrix i left) (toMatrix i right)).d -
            (i ^ 2 + 1) * (left.vector.r * right.vector.r + left.vector.s * right.vector.s) := by
        unfold toMatrix Proportion.mul Vector3.dot Vector3.sub Vector3.add Vector3.scale
          Vector3.cross Matrix2.mul
        ring1
      _ = (Matrix2.mul (toMatrix i left) (toMatrix i right)).d := by rw [iSquare]; ring1

/-- Recover quaternion coordinates from a matrix using half-sums and the inverse imaginary unit.

When both two and the supplied imaginary unit are nonzero, decoding is the
inverse of the matrix encoding. No normalization or scalar root is chosen.
-/
@[expose] def fromMatrix (i : K) (matrix : Matrix2 K) : Proportion K :=
  ⟨(2 : K)⁻¹ * (matrix.a + matrix.d),
    ⟨(2 : K)⁻¹ * (matrix.c - matrix.b),
      (2 : K)⁻¹ * i⁻¹ * (matrix.b + matrix.c),
      (2 : K)⁻¹ * i⁻¹ * (matrix.a - matrix.d)⟩⟩

/-- Decoding a quaternion matrix recovers the original quaternion.

The two nonzero certificates justify precisely the two divisions in the
coordinate recovery formula.
-/
theorem fromMatrix_toMatrix (i : K) (iNonzero : i ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (value : Proportion K) : fromMatrix i (toMatrix i value) = value := by
  have cancelTwo := ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  have cancelI := ExplicitField.mul_inv_cancel i iNonzero
  apply Proportion.ext
  · change (2 : K)⁻¹ * (value.scalar + i * value.vector.s +
      (value.scalar - i * value.vector.s)) = value.scalar
    calc
      _ = value.scalar * ((2 : K) * (2 : K)⁻¹) := by ring1
      _ = value.scalar := by rw [cancelTwo, mul_one]
  · apply Vector3.ext
    · change (2 : K)⁻¹ * (value.vector.t + i * value.vector.r -
        (-value.vector.t + i * value.vector.r)) = value.vector.t
      calc
        _ = value.vector.t * ((2 : K) * (2 : K)⁻¹) := by ring1
        _ = value.vector.t := by rw [cancelTwo, mul_one]
    · change (2 : K)⁻¹ * i⁻¹ * (-value.vector.t + i * value.vector.r +
        (value.vector.t + i * value.vector.r)) = value.vector.r
      calc
        _ = value.vector.r * ((2 : K) * (2 : K)⁻¹) * (i * i⁻¹) := by ring1
        _ = value.vector.r := by rw [cancelTwo, cancelI, mul_one, mul_one]
    · change (2 : K)⁻¹ * i⁻¹ * (value.scalar + i * value.vector.s -
        (value.scalar - i * value.vector.s)) = value.vector.s
      calc
        _ = value.vector.s * ((2 : K) * (2 : K)⁻¹) * (i * i⁻¹) := by ring1
        _ = value.vector.s := by rw [cancelTwo, cancelI, mul_one, mul_one]

/-- Encoding decoded coordinates returns the original two-by-two matrix.

Together with coordinate recovery, this is the full matrix-algebra
bijection when the ground field contains a nonzero imaginary unit.
-/
theorem toMatrix_fromMatrix (i : K) (iNonzero : i ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (matrix : Matrix2 K) : toMatrix i (fromMatrix i matrix) = matrix := by
  have cancelTwo := ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  have cancelI := ExplicitField.mul_inv_cancel i iNonzero
  have removeI (entry : K) : i * ((2 : K)⁻¹ * i⁻¹ * entry) = (2 : K)⁻¹ * entry := by
    calc
      _ = ((2 : K)⁻¹ * entry) * (i * i⁻¹) := by ring1
      _ = (2 : K)⁻¹ * entry := by rw [cancelI, mul_one]
  apply Matrix2.ext
  · change (2 : K)⁻¹ * (matrix.a + matrix.d) + i * ((2 : K)⁻¹ * i⁻¹ * (matrix.a - matrix.d)) = matrix.a
    rw [removeI]
    calc
      _ = matrix.a * ((2 : K) * (2 : K)⁻¹) := by ring1
      _ = matrix.a := by rw [cancelTwo, mul_one]
  · change -((2 : K)⁻¹ * (matrix.c - matrix.b)) + i * ((2 : K)⁻¹ * i⁻¹ * (matrix.b + matrix.c)) = matrix.b
    rw [removeI]
    calc
      _ = matrix.b * ((2 : K) * (2 : K)⁻¹) := by ring1
      _ = matrix.b := by rw [cancelTwo, mul_one]
  · change (2 : K)⁻¹ * (matrix.c - matrix.b) + i * ((2 : K)⁻¹ * i⁻¹ * (matrix.b + matrix.c)) = matrix.c
    rw [removeI]
    calc
      _ = matrix.c * ((2 : K) * (2 : K)⁻¹) := by ring1
      _ = matrix.c := by rw [cancelTwo, mul_one]
  · change (2 : K)⁻¹ * (matrix.a + matrix.d) - i * ((2 : K)⁻¹ * i⁻¹ * (matrix.a - matrix.d)) = matrix.d
    rw [removeI]
    calc
      _ = matrix.d * ((2 : K) * (2 : K)⁻¹) := by ring1
      _ = matrix.d := by rw [cancelTwo, mul_one]

/-- Equal matrix encodings imply equal quaternion coordinates. -/
theorem toMatrix_injective (i : K) (iNonzero : i ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    {left right : Proportion K} (equal : toMatrix i left = toMatrix i right) : left = right := by
  calc
    left = fromMatrix i (toMatrix i left) := (fromMatrix_toMatrix i iNonzero twoNonzero left).symm
    _ = fromMatrix i (toMatrix i right) := congrArg (fromMatrix i) equal
    _ = right := fromMatrix_toMatrix i iNonzero twoNonzero right

/-- Quaternion matrix encoding preserves coordinate addition. -/
theorem toMatrix_add (i : K) (left right : Proportion K) :
    toMatrix i (Proportion.add left right) = Matrix2.add (toMatrix i left) (toMatrix i right) := by
  apply Matrix2.ext <;> unfold toMatrix Proportion.add Vector3.add Matrix2.add <;> ring1

/-- Quaternion matrix encoding preserves scalar multiplication. -/
theorem toMatrix_scale (i factor : K) (value : Proportion K) :
    toMatrix i (Proportion.scale factor value) = Matrix2.scalarScale factor (toMatrix i value) := by
  apply Matrix2.ext <;> unfold toMatrix Proportion.scale Vector3.scale Matrix2.scalarScale <;> ring1

/-- The squared matrix trace divided by four times its determinant is the scalar-square norm ratio.

The unit squares to negative one, and both two and the quaternion norm are
nonzero. These certificates justify the denominator cancellations in the ratio.
-/
theorem trace_square_ratio (i : K) (iSquare : i ^ 2 = -1) (twoNonzero : (2 : K) ≠ 0)
    (value : Proportion K) (normNonzero : value.norm ≠ 0) :
    (Matrix2.trace (toMatrix i value)) ^ 2 / (4 * Matrix2.determinant (toMatrix i value)) =
      value.scalar ^ 2 / value.norm := by
  have fourNonzero := four_ne_zero twoNonzero
  have cancelFour := ExplicitField.mul_inv_cancel (4 : K) fourNonzero
  change ((toMatrix i value).a + (toMatrix i value).d) ^ 2 / _ = _
  rw [diagonal_sum_toMatrix, determinant_toMatrix i iSquare,
    ExplicitField.div_eq_mul_inv, ExplicitField.div_eq_mul_inv,
    Field.Inverse.inverse_product fourNonzero normNonzero]
  calc
    (2 * value.scalar) ^ 2 * ((4 : K)⁻¹ * value.norm⁻¹) =
        (4 * (4 : K)⁻¹) * (value.scalar ^ 2 * value.norm⁻¹) := by ring1
    _ = value.scalar ^ 2 * value.norm⁻¹ := by rw [cancelFour, one_mul]

/-- Encode the original quaternion over an explicitly embedded coefficient field.

The supplied embedding transports each retained coordinate, and the displayed
imaginary unit belongs to that target field. The original quaternion remains
the input owner; its norm and operations are transported by the same map.
-/
@[expose] def toEmbeddedMatrix {L : Type*} [ExplicitField L] [DecidableEq K] [DecidableEq L]
    (embedding : Embedding K L) (i : L) (value : Proportion K) : Matrix2 L :=
  toMatrix i (Proportion.map embedding value)

/-- Embedded quaternion matrices preserve the original product. -/
theorem toEmbeddedMatrix_mul {L : Type*} [ExplicitField L] [DecidableEq K] [DecidableEq L]
    (embedding : Embedding K L) (i : L) (iSquare : i ^ 2 = -1) (left right : Proportion K) :
    toEmbeddedMatrix embedding i (Proportion.mul left right) =
      Matrix2.mul (toEmbeddedMatrix embedding i left) (toEmbeddedMatrix embedding i right) := by
  unfold toEmbeddedMatrix
  rw [Proportion.map_mul, toMatrix_mul i iSquare]

/-- Embedded quaternion matrices preserve addition of the original coordinates. -/
theorem toEmbeddedMatrix_add {L : Type*} [ExplicitField L] [DecidableEq K] [DecidableEq L]
    (embedding : Embedding K L) (i : L) (left right : Proportion K) :
    toEmbeddedMatrix embedding i (Proportion.add left right) =
      Matrix2.add (toEmbeddedMatrix embedding i left) (toEmbeddedMatrix embedding i right) := by
  unfold toEmbeddedMatrix
  rw [Proportion.map_add, toMatrix_add]

/-- Embedded quaternion matrices preserve scaling by the embedded original coefficient. -/
theorem toEmbeddedMatrix_scale {L : Type*} [ExplicitField L] [DecidableEq K] [DecidableEq L]
    (embedding : Embedding K L) (i : L) (factor : K) (value : Proportion K) :
    toEmbeddedMatrix embedding i (Proportion.scale factor value) =
      Matrix2.scalarScale (embedding.toFun factor) (toEmbeddedMatrix embedding i value) := by
  unfold toEmbeddedMatrix
  rw [Proportion.map_scale, toMatrix_scale]

/-- The embedded quaternion determinant is the image of its original norm. -/
theorem determinant_toEmbeddedMatrix {L : Type*} [ExplicitField L] [DecidableEq K] [DecidableEq L]
    (embedding : Embedding K L) (i : L) (iSquare : i ^ 2 = -1) (value : Proportion K) :
    Matrix2.determinant (toEmbeddedMatrix embedding i value) = embedding.toFun value.norm := by
  unfold toEmbeddedMatrix
  rw [determinant_toMatrix i iSquare, Proportion.map_norm]

/-- The embedded matrix trace is twice the image of the original scalar coordinate. -/
theorem trace_toEmbeddedMatrix {L : Type*} [ExplicitField L] [DecidableEq K] [DecidableEq L]
    (embedding : Embedding K L) (i : L) (value : Proportion K) :
    Matrix2.trace (toEmbeddedMatrix embedding i value) = 2 * embedding.toFun value.scalar :=
  diagonal_sum_toMatrix i (Proportion.map embedding value)

/-- Original quaternion conjugation becomes adjugation of the embedded matrix. -/
theorem toEmbeddedMatrix_conjugate {L : Type*} [ExplicitField L] [DecidableEq K] [DecidableEq L]
    (embedding : Embedding K L) (i : L) (value : Proportion K) :
    toEmbeddedMatrix embedding i (Proportion.conjugate value) =
      Matrix2.adjugate (toEmbeddedMatrix embedding i value) := by
  unfold toEmbeddedMatrix
  rw [Proportion.map_conjugate, toMatrix_conjugate]

/-- Embedded quaternion matrix encoding is injective on the original quaternion coordinates.

The supplied nonzero target unit and nonzero target two give matrix coordinate
recovery. The retained field embedding then reflects equality in each input
coordinate.
-/
theorem toEmbeddedMatrix_injective {L : Type*} [ExplicitField L] [DecidableEq K] [DecidableEq L]
    (embedding : Embedding K L) (i : L) (iNonzero : i ≠ 0) (twoNonzero : (2 : L) ≠ 0)
    {left right : Proportion K} (equal : toEmbeddedMatrix embedding i left = toEmbeddedMatrix embedding i right) :
    left = right :=
  Proportion.map_injective embedding (toMatrix_injective i iNonzero twoNonzero equal)

/-- The embedded squared-trace ratio is the image of the original scalar-square norm ratio.

The input norm is retained and transported by the supplied embedding. Its
nonzero certificate reflects through that same map, while the supplied target
two certifies cancellation of four in the matrix ratio.
-/
theorem embedded_trace_square_ratio {L : Type*} [ExplicitField L] [DecidableEq K] [DecidableEq L]
    (embedding : Embedding K L) (i : L) (iSquare : i ^ 2 = -1) (twoNonzero : (2 : L) ≠ 0)
    (value : Proportion K) (normNonzero : value.norm ≠ 0) :
    (Matrix2.trace (toEmbeddedMatrix embedding i value)) ^ 2 /
        (4 * Matrix2.determinant (toEmbeddedMatrix embedding i value)) =
      embedding.toFun (value.scalar ^ 2 / value.norm) := by
  have imageNormNonzero : (Proportion.map embedding value).norm ≠ 0 := by
    rw [Proportion.map_norm]
    intro zero
    exact normNonzero ((embedding.map_zero_iff value.norm).mp zero)
  unfold toEmbeddedMatrix
  rw [trace_square_ratio i iSquare twoNonzero _ imageNormNonzero, Proportion.map_norm, embedding.map_div]
  change (embedding.toFun value.scalar) ^ 2 / embedding.toFun value.norm =
    embedding.toFun (value.scalar ^ 2) / embedding.toFun value.norm
  rw [pow_two, pow_two, embedding.map_mul]

/-- The original imaginary quadratic field gives the literal four-entry quaternion matrix.

Each entry is an original pair of ground-field coordinates. This identifies
the matrix built through the certified scalar embedding with the displayed
real and imaginary coordinates, while retaining its target field dictionary.
-/
theorem toEmbeddedMatrix_imaginaryField [DecidableEq K]
    (noRoot : Field.Squares.NoSquareRootOfNegativeOne (K := K)) (twoNonzero : (2 : K) ≠ 0)
    (value : Proportion K) :
    letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
    toEmbeddedMatrix (Quadratic.Pair.ImaginaryField.scalarEmbedding noRoot twoNonzero)
      Quadratic.Pair.generator value =
        ⟨⟨value.scalar, value.vector.s⟩, ⟨-value.vector.t, value.vector.r⟩,
          ⟨value.vector.t, value.vector.r⟩, ⟨value.scalar, -value.vector.s⟩⟩ := by
  letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
  apply Matrix2.ext <;> apply Quadratic.Pair.ext <;>
    simp only [toEmbeddedMatrix, toMatrix, Proportion.map, Quadratic.Pair.ImaginaryField.scalarEmbedding,
      Quadratic.Pair.generator, Quadratic.Pair.scalar, Quadratic.Pair.add_re, Quadratic.Pair.add_im,
      Quadratic.Pair.mul_re, Quadratic.Pair.mul_im, Quadratic.Pair.neg_re, Quadratic.Pair.neg_im,
      Quadratic.Pair.sub_re, Quadratic.Pair.sub_im, -eq_self, -iff_self] <;> ring1

/-- The formal-imaginary quaternion matrix has conjugate transpose equal to its adjugate.

The same embedded ground-field quaternion supplies all entries. The original
pair conjugation reverses its imaginary coordinates and transposition places
the conjugated off-diagonal entries in the adjugate positions.
-/
theorem conjugateTranspose_toEmbeddedMatrix [DecidableEq K]
    (noRoot : Field.Squares.NoSquareRootOfNegativeOne (K := K)) (twoNonzero : (2 : K) ≠ 0)
    (value : Proportion K) :
    letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
    let matrix := toEmbeddedMatrix (Quadratic.Pair.ImaginaryField.scalarEmbedding noRoot twoNonzero)
      Quadratic.Pair.generator value
    Matrix2.conjugateTranspose Quadratic.Pair.conjugate matrix = Matrix2.adjugate matrix := by
  letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
  rw [toEmbeddedMatrix_imaginaryField]
  apply Matrix2.ext <;> apply Quadratic.Pair.ext <;>
    simp only [Matrix2.conjugateTranspose, Matrix2.transpose, Matrix2.map, Matrix2.adjugate,
      Quadratic.Pair.conjugate, Quadratic.Pair.neg_re, Quadratic.Pair.neg_im, -eq_self, -iff_self] <;> ring1

/-- A ground-field quaternion has norm one exactly when its formal-imaginary matrix is unitary with determinant one.

Both unitary equations concern the same original embedded matrix. Its
conjugate transpose is its adjugate, and its determinant is the embedded
original norm; real-coordinate readback reflects the determinant equality.
-/
theorem norm_one_iff_special_unitary [DecidableEq K]
    (noRoot : Field.Squares.NoSquareRootOfNegativeOne (K := K)) (twoNonzero : (2 : K) ≠ 0)
    (value : Proportion K) :
    letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
    let matrix := toEmbeddedMatrix (Quadratic.Pair.ImaginaryField.scalarEmbedding noRoot twoNonzero)
      Quadratic.Pair.generator value
    value.norm = 1 ↔ Matrix2.determinant matrix = 1 ∧ Matrix2.IsUnitary Quadratic.Pair.conjugate matrix := by
  letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
  let embedding := Quadratic.Pair.ImaginaryField.scalarEmbedding noRoot twoNonzero
  let matrix := toEmbeddedMatrix embedding Quadratic.Pair.generator value
  have adjoint := conjugateTranspose_toEmbeddedMatrix noRoot twoNonzero value
  have determinant := determinant_toEmbeddedMatrix embedding Quadratic.Pair.generator
    Quadratic.Pair.ImaginaryField.generator_square value
  have scaleOne : Matrix2.scalarScale (1 : Quadratic.Pair K (1 : K)) Matrix2.identity = Matrix2.identity := by
    apply Matrix2.ext <;> dsimp only [Matrix2.scalarScale, Matrix2.identity] <;> rw [one_mul]
  constructor
  · intro normOne
    have determinantOne : Matrix2.determinant matrix = 1 := by
      rw [determinant, normOne, embedding.map_one]
    refine ⟨determinantOne, ?_, ?_⟩
    · change Matrix2.mul (Matrix2.conjugateTranspose Quadratic.Pair.conjugate matrix) matrix = _
      rw [adjoint, Matrix2.adjugate_mul, determinantOne]
      exact scaleOne
    · change Matrix2.mul matrix (Matrix2.conjugateTranspose Quadratic.Pair.conjugate matrix) = _
      rw [adjoint, Matrix2.mul_adjugate, determinantOne]
      exact scaleOne
  · intro certificate
    exact embedding.injective (determinant.symm.trans (certificate.1.trans embedding.map_one.symm))

/-- The imaginary-extension quaternion image is exactly the twisted conjugation fixed locus.

Entrywise conjugation is the original pair conjugation. The two displayed
constant matrices are `J` and its inverse. A fixed matrix is reconstructed
from its upper-left entry and lower-left entry, giving an explicit original
ground-field quaternion rather than a dimension or choice argument.
-/
theorem imaginary_image_iff_fixed [DecidableEq K]
    (noRoot : Field.Squares.NoSquareRootOfNegativeOne (K := K)) (twoNonzero : (2 : K) ≠ 0)
    (matrix : Matrix2 (Quadratic.Pair K (1 : K))) :
    letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
    (∃ value : Proportion K,
      toEmbeddedMatrix (Quadratic.Pair.ImaginaryField.scalarEmbedding noRoot twoNonzero)
        Quadratic.Pair.generator value = matrix) ↔
      Matrix2.mul (Matrix2.mul ⟨0, -1, 1, 0⟩ matrix) ⟨0, 1, -1, 0⟩ =
        Matrix2.map Quadratic.Pair.conjugate matrix := by
  letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
  constructor
  · rintro ⟨value, image⟩
    rw [← image, toEmbeddedMatrix_imaginaryField]
    apply Matrix2.ext <;> apply Quadratic.Pair.ext <;>
      simp only [Matrix2.mul, Matrix2.map, Quadratic.Pair.conjugate,
        Quadratic.Pair.add_re, Quadratic.Pair.add_im, Quadratic.Pair.mul_re, Quadratic.Pair.mul_im,
        Quadratic.Pair.neg_re, Quadratic.Pair.neg_im, Quadratic.Pair.zero_re, Quadratic.Pair.zero_im,
        Quadratic.Pair.one_re, Quadratic.Pair.one_im, -eq_self, -iff_self] <;> ring1
  · intro fixed
    have bReal := congrArg (fun value => value.b.re) fixed
    have bImaginary := congrArg (fun value => value.b.im) fixed
    have dReal := congrArg (fun value => value.d.re) fixed
    have dImaginary := congrArg (fun value => value.d.im) fixed
    simp only [Matrix2.mul, Matrix2.map, Quadratic.Pair.conjugate,
      Quadratic.Pair.neg_re, Quadratic.Pair.neg_im, zero_mul, mul_zero, one_mul, mul_one,
      neg_mul, mul_neg, neg_neg, zero_add, add_zero, -eq_self, -iff_self]
      at bReal bImaginary dReal dImaginary
    refine ⟨⟨matrix.a.re, ⟨matrix.c.re, matrix.c.im, matrix.a.im⟩⟩, ?_⟩
    rw [toEmbeddedMatrix_imaginaryField]
    apply Matrix2.ext
    · rfl
    · apply Quadratic.Pair.ext
      · exact bReal
      · calc
          matrix.c.im = -(-matrix.c.im) := by ring1
          _ = -(-matrix.b.im) := congrArg Neg.neg bImaginary
          _ = matrix.b.im := by ring1
    · rfl
    · apply Quadratic.Pair.ext
      · exact dReal
      · calc
          -matrix.a.im = -(-matrix.d.im) := congrArg Neg.neg dImaginary
          _ = matrix.d.im := by ring1

/-- Every unitary determinant-one matrix over the formal imaginary field comes from an original norm-one quaternion.

The unitary left inverse equals the determinant-one adjugate by associativity.
Its four entries give the original twisted-conjugation fixed condition, whose
coordinate reconstruction supplies the ground-field quaternion explicitly.
-/
theorem special_unitary_iff_unit_quaternion [DecidableEq K]
    (noRoot : Field.Squares.NoSquareRootOfNegativeOne (K := K)) (twoNonzero : (2 : K) ≠ 0)
    (matrix : Matrix2 (Quadratic.Pair K (1 : K))) :
    letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
    (Matrix2.determinant matrix = 1 ∧ Matrix2.IsUnitary Quadratic.Pair.conjugate matrix) ↔
      ∃ value : Proportion K, value.norm = 1 ∧
        toEmbeddedMatrix (Quadratic.Pair.ImaginaryField.scalarEmbedding noRoot twoNonzero)
          Quadratic.Pair.generator value = matrix := by
  letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
  constructor
  · intro certificate
    have rightInverse : Matrix2.mul matrix (Matrix2.adjugate matrix) = Matrix2.identity := by
      rw [Matrix2.mul_adjugate, certificate.1]
      apply Matrix2.ext <;> dsimp only [Matrix2.scalarScale, Matrix2.identity] <;> rw [one_mul]
    have adjointEq : Matrix2.conjugateTranspose Quadratic.Pair.conjugate matrix = Matrix2.adjugate matrix := by
      calc
        _ = Matrix2.mul (Matrix2.conjugateTranspose Quadratic.Pair.conjugate matrix) Matrix2.identity :=
          (Matrix2.mul_identity _).symm
        _ = Matrix2.mul (Matrix2.conjugateTranspose Quadratic.Pair.conjugate matrix)
            (Matrix2.mul matrix (Matrix2.adjugate matrix)) :=
          congrArg (Matrix2.mul (Matrix2.conjugateTranspose Quadratic.Pair.conjugate matrix)) rightInverse.symm
        _ = Matrix2.mul (Matrix2.mul (Matrix2.conjugateTranspose Quadratic.Pair.conjugate matrix) matrix)
            (Matrix2.adjugate matrix) := (Matrix2.mul_assoc _ _ _).symm
        _ = Matrix2.adjugate matrix := by rw [certificate.2.1, Matrix2.identity_mul]
    have first := congrArg Matrix2.a adjointEq
    have second := congrArg Matrix2.b adjointEq
    have third := congrArg Matrix2.c adjointEq
    have fourth := congrArg Matrix2.d adjointEq
    change matrix.a.conjugate = matrix.d at first
    change matrix.c.conjugate = -matrix.b at second
    change matrix.b.conjugate = -matrix.c at third
    change matrix.d.conjugate = matrix.a at fourth
    have fixed : Matrix2.mul (Matrix2.mul ⟨0, -1, 1, 0⟩ matrix) ⟨0, 1, -1, 0⟩ =
        Matrix2.map Quadratic.Pair.conjugate matrix := by
      have coordinates : Matrix2.mul (Matrix2.mul ⟨0, -1, 1, 0⟩ matrix) ⟨0, 1, -1, 0⟩ =
          ⟨matrix.d, -matrix.c, -matrix.b, matrix.a⟩ := by
        apply Matrix2.ext <;> unfold Matrix2.mul <;> ring1
      rw [coordinates]
      exact Matrix2.ext first.symm third.symm second.symm fourth.symm
    rcases (imaginary_image_iff_fixed noRoot twoNonzero matrix).mpr fixed with ⟨value, image⟩
    refine ⟨value, ?_, image⟩
    apply (norm_one_iff_special_unitary noRoot twoNonzero value).mpr
    rw [image]
    exact certificate
  · rintro ⟨value, normOne, image⟩
    have certificate := (norm_one_iff_special_unitary noRoot twoNonzero value).mp normOne
    rw [image] at certificate
    exact certificate

/-- Entrywise conjugation fixes exactly the matrices with scalar-pair coefficients.

Nonzero two forces each fixed imaginary coordinate to vanish. The matrix of
real coordinates supplies a constructive ground-field preimage, identifying
the untwisted fixed algebra with the original two-by-two matrix algebra.
-/
theorem conjugation_fixed_iff_base_matrix (twoNonzero : (2 : K) ≠ 0)
    (matrix : Matrix2 (Quadratic.Pair K (1 : K))) :
    Matrix2.map Quadratic.Pair.conjugate matrix = matrix ↔
      ∃ base : Matrix2 K, Matrix2.map Quadratic.Pair.scalar base = matrix := by
  have scalarOfFixed (value : Quadratic.Pair K (1 : K)) (fixed : value.conjugate = value) :
      Quadratic.Pair.scalar value.re = value := by
    have imaginary := congrArg Quadratic.Pair.im fixed
    have doubledZero : 2 * value.im = 0 := by
      calc
        2 * value.im = value.im - (-value.im) := by ring1
        _ = value.im - value.im := congrArg (fun coefficient => value.im - coefficient) imaginary
        _ = 0 := by ring1
    have imaginaryZero : value.im = 0 :=
      ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero doubledZero
    exact Quadratic.Pair.ext rfl imaginaryZero.symm
  constructor
  · intro fixed
    refine ⟨⟨matrix.a.re, matrix.b.re, matrix.c.re, matrix.d.re⟩, ?_⟩
    apply Matrix2.ext
    · exact scalarOfFixed matrix.a (congrArg Matrix2.a fixed)
    · exact scalarOfFixed matrix.b (congrArg Matrix2.b fixed)
    · exact scalarOfFixed matrix.c (congrArg Matrix2.c fixed)
    · exact scalarOfFixed matrix.d (congrArg Matrix2.d fixed)
  · rintro ⟨base, image⟩
    rw [← image]
    apply Matrix2.ext <;> apply Quadratic.Pair.ext <;>
      simp only [Matrix2.map, Quadratic.Pair.conjugate, Quadratic.Pair.scalar, -eq_self, -iff_self] <;> ring1

end Purelib.Algebra.Quaternion.Matrix
