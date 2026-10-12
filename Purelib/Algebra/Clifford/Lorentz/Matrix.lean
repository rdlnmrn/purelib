module

public import Purelib.Algebra.Quadratic.Ternary.Lorentz
public import Purelib.Algebra.Clifford.Ternary.Action
import Purelib.LinearAlgebra.Coordinates2.Matrix
public import Purelib.LinearAlgebra.Coordinates2.RankOne
public import Purelib.LinearAlgebra.Coordinates2.Invertible
public import Purelib.Geometry.Quadratic.Ternary.Lorentz
import Purelib.Algebra.Clifford.Ternary.Basic
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring

/-!
# Time-first dihedron coordinates and their matrix model

The paper's vector coordinate is the negative of the determinant-one
Clifford vector coordinate. This explicit conversion keeps the original
form owner and makes the paper's row-action product and matrix agree.
-/

public section

namespace Purelib.Algebra.Clifford.Lorentz.Matrix

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Quadratic.Ternary.Basic (TernaryForm)
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm
open Purelib.Geometry.Quadratic.Ternary
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)

variable {K : Type*} [ExplicitField K]

/-- Encode scalar and time-first vector coordinates in the Lorentz Clifford algebra.

Negating the vector converts the paper's cross-product convention to the
adjugate-cross convention of the original Clifford owner.
-/
@[expose] def coordinates (oneNonzero : (1 : K) ≠ 0) (scalar : K) (vector : Vector3 K) :
    (TernaryForm.lorentz oneNonzero).EvenClifford := ⟨scalar, Vector3.neg vector⟩

/-- Encode a Lorentz Clifford value as a two-by-two matrix over its scalar field. -/
@[expose] def toMatrix (oneNonzero : (1 : K) ≠ 0)
    (value : (TernaryForm.lorentz oneNonzero).EvenClifford) : Matrix2 K :=
  ⟨value.scalar - value.vector.s, value.vector.t - value.vector.r,
    -value.vector.r - value.vector.t, value.scalar + value.vector.s⟩

/-- Recover Lorentz Clifford coordinates from a matrix by half-sums and differences. -/
@[expose] def fromMatrix (oneNonzero : (1 : K) ≠ 0) (matrix : Matrix2 K) :
    (TernaryForm.lorentz oneNonzero).EvenClifford :=
  ⟨(2 : K)⁻¹ * (matrix.a + matrix.d),
    ⟨(2 : K)⁻¹ * (matrix.b - matrix.c), -(2 : K)⁻¹ * (matrix.b + matrix.c),
      (2 : K)⁻¹ * (matrix.d - matrix.a)⟩⟩

/-- The coordinate conversion gives the displayed dihedron matrix literally. -/
theorem toMatrix_coordinates (oneNonzero : (1 : K) ≠ 0) (scalar : K) (vector : Vector3 K) :
    toMatrix oneNonzero (coordinates oneNonzero scalar vector) =
      (⟨scalar + vector.s, vector.r - vector.t, vector.r + vector.t, scalar - vector.s⟩ : Matrix2 K) := by
  ext <;> unfold toMatrix coordinates Vector3.neg <;> ring1

/-- The matrix trace of a source dihedron is twice its retained scalar coordinate. -/
theorem trace_coordinates (oneNonzero : (1 : K) ≠ 0) (scalar : K) (vector : Vector3 K) :
    Matrix2.trace (toMatrix oneNonzero (coordinates oneNonzero scalar vector)) = 2 * scalar := by
  rw [toMatrix_coordinates]
  unfold Matrix2.trace
  ring1

/-- The source coordinate map preserves addition in the original Clifford algebra. -/
theorem coordinates_add (oneNonzero : (1 : K) ≠ 0) (leftScalar rightScalar : K)
    (leftVector rightVector : Vector3 K) :
    coordinates oneNonzero (leftScalar + rightScalar) (Vector3.add leftVector rightVector) =
      EvenClifford.add (coordinates oneNonzero leftScalar leftVector)
        (coordinates oneNonzero rightScalar rightVector) := by
  apply TernaryForm.EvenClifford.ext
  · rfl
  · ext <;> unfold coordinates EvenClifford.add Vector3.add Vector3.neg <;> ring1

/-- The matrix model preserves addition of original Clifford representatives. -/
theorem toMatrix_add (oneNonzero : (1 : K) ≠ 0)
    (left right : (TernaryForm.lorentz oneNonzero).EvenClifford) :
    toMatrix oneNonzero (EvenClifford.add left right) =
      Matrix2.add (toMatrix oneNonzero left) (toMatrix oneNonzero right) := by
  ext <;> unfold toMatrix EvenClifford.add Matrix2.add Vector3.add <;> ring1

/-- The matrix model preserves homogeneous scalar multiplication of original Clifford representatives. -/
theorem toMatrix_scale (oneNonzero : (1 : K) ≠ 0) (factor : K)
    (value : (TernaryForm.lorentz oneNonzero).EvenClifford) :
    toMatrix oneNonzero (EvenClifford.scale factor value) = Matrix2.scalarScale factor (toMatrix oneNonzero value) := by
  ext <;> unfold toMatrix EvenClifford.scale Matrix2.scalarScale Vector3.scale <;> ring1

/-- The original Clifford product has the paper's scalar pairing and signed vector numerator in source coordinates.

The source vector is negated in the retained Clifford coordinate. This
conversion gives scalar `xy - B(v,u)` and vector `xu + yv - cross(v,u)`
with the original row-action multiplication order.
-/
theorem coordinates_mul (oneNonzero : (1 : K) ≠ 0) (leftScalar rightScalar : K)
    (leftVector rightVector : Vector3 K) :
    EvenClifford.mul (coordinates oneNonzero leftScalar leftVector)
        (coordinates oneNonzero rightScalar rightVector) =
      coordinates oneNonzero
        (leftScalar * rightScalar - (TernaryForm.lorentz oneNonzero).bilinear leftVector rightVector)
        (Vector3.sub (Vector3.add (Vector3.scale leftScalar rightVector) (Vector3.scale rightScalar leftVector))
          (Lorentz.cross oneNonzero leftVector rightVector)) := by
  apply TernaryForm.EvenClifford.ext
  · change leftScalar * rightScalar - (TernaryForm.lorentz oneNonzero).determinant *
      (TernaryForm.lorentz oneNonzero).bilinear (Vector3.neg leftVector) (Vector3.neg rightVector) =
      leftScalar * rightScalar - (TernaryForm.lorentz oneNonzero).bilinear leftVector rightVector
    rw [TernaryForm.lorentz_determinant, TernaryForm.bilinear_neg_left, TernaryForm.bilinear_neg_right]
    ring1
  · change Vector3.sub
      (Vector3.add (Vector3.scale leftScalar (Vector3.neg rightVector))
        (Vector3.scale rightScalar (Vector3.neg leftVector)))
      ((TernaryForm.lorentz oneNonzero).cliffordCross (Vector3.neg leftVector) (Vector3.neg rightVector)) = _
    rw [TernaryForm.cliffordCross_neg_left, TernaryForm.cliffordCross_neg_right, Vector3.neg_neg]
    unfold coordinates Lorentz.cross
    ext <;> unfold Vector3.add Vector3.sub Vector3.scale Vector3.neg <;> ring1

/-- The dihedron norm is the scalar square plus the original source vector quadrance. -/
theorem norm_coordinates_quadrance (oneNonzero : (1 : K) ≠ 0) (scalar : K) (vector : Vector3 K) :
    EvenClifford.norm (coordinates oneNonzero scalar vector) =
      scalar ^ 2 + (TernaryForm.lorentz oneNonzero).quadrance vector := by
  change scalar ^ 2 + (TernaryForm.lorentz oneNonzero).determinant *
    (TernaryForm.lorentz oneNonzero).quadrance (Vector3.neg vector) = _
  rw [TernaryForm.lorentz_determinant, TernaryForm.quadrance_neg, one_mul]

/-- Retain a non-null source dihedron in the original form-indexed Clifford owner.

The supplied certificate proves that the scalar square plus the source
vector quadrance is nonzero. The construction retains the scalar and
negates the source vector in the original Clifford parent.
-/
@[expose] def nonNullCoordinates (oneNonzero : (1 : K) ≠ 0) (scalar : K) (vector : Vector3 K)
    (defined : scalar ^ 2 + (TernaryForm.lorentz oneNonzero).quadrance vector ≠ 0) :
    (TernaryForm.lorentz oneNonzero).NonNullEvenClifford where
  toEvenClifford := coordinates oneNonzero scalar vector
  normNonzero := by rw [norm_coordinates_quadrance]; exact defined

/-- Source vector negation is the original dihedron conjugation. -/
theorem coordinates_conjugate (oneNonzero : (1 : K) ≠ 0) (scalar : K) (vector : Vector3 K) :
    EvenClifford.conjugate (coordinates oneNonzero scalar vector) =
      coordinates oneNonzero scalar (Vector3.neg vector) := rfl

/-- The time basis element of the source dihedron algebra. -/
@[expose] def i (oneNonzero : (1 : K) ≠ 0) : (TernaryForm.lorentz oneNonzero).EvenClifford :=
  coordinates oneNonzero 0 ⟨1, 0, 0⟩

/-- The first space basis element of the source dihedron algebra. -/
@[expose] def j (oneNonzero : (1 : K) ≠ 0) : (TernaryForm.lorentz oneNonzero).EvenClifford :=
  coordinates oneNonzero 0 ⟨0, 1, 0⟩

/-- The second space basis element of the source dihedron algebra. -/
@[expose] def k (oneNonzero : (1 : K) ≠ 0) : (TernaryForm.lorentz oneNonzero).EvenClifford :=
  coordinates oneNonzero 0 ⟨0, 0, 1⟩

/-- Every source dihedron is the sum of its scalar identity and its three retained basis components. -/
theorem coordinates_basis_decomposition (oneNonzero : (1 : K) ≠ 0) (scalar : K) (vector : Vector3 K) :
    coordinates oneNonzero scalar vector =
      EvenClifford.add (EvenClifford.scale scalar (EvenClifford.identity (TernaryForm.lorentz oneNonzero)))
        (EvenClifford.add (EvenClifford.scale vector.t (i oneNonzero))
          (EvenClifford.add (EvenClifford.scale vector.r (j oneNonzero))
            (EvenClifford.scale vector.s (k oneNonzero)))) := by
  apply TernaryForm.EvenClifford.ext
  · dsimp only [coordinates, i, j, k, EvenClifford.add, EvenClifford.scale, EvenClifford.identity]
    ring1
  · ext <;> dsimp only [coordinates, i, j, k, EvenClifford.add, EvenClifford.scale,
      EvenClifford.identity, Vector3.add, Vector3.scale, Vector3.neg, Vector3.zero] <;> ring1

/-- The three original dihedron basis elements have the displayed two-by-two matrices. -/
theorem basis_matrices (oneNonzero : (1 : K) ≠ 0) :
    toMatrix oneNonzero (i oneNonzero) = (⟨0, -1, 1, 0⟩ : Matrix2 K) ∧
    toMatrix oneNonzero (j oneNonzero) = (⟨0, 1, 1, 0⟩ : Matrix2 K) ∧
    toMatrix oneNonzero (k oneNonzero) = (⟨1, 0, 0, -1⟩ : Matrix2 K) := by
  refine ⟨?_, ?_, ?_⟩ <;> ext <;> dsimp only [i, j, k, toMatrix, coordinates, Vector3.neg] <;> ring1

/-- The original dihedron basis products have the source row-action multiplication table.

The time basis squares to negative identity, while both space bases
square to identity. The six mixed products retain their ordered signs;
reversing their order negates the resulting basis element.
-/
theorem basis_table (oneNonzero : (1 : K) ≠ 0) :
    EvenClifford.mul (i oneNonzero) (i oneNonzero) =
      EvenClifford.scale (-1) (EvenClifford.identity (TernaryForm.lorentz oneNonzero)) ∧
    EvenClifford.mul (j oneNonzero) (j oneNonzero) = EvenClifford.identity (TernaryForm.lorentz oneNonzero) ∧
    EvenClifford.mul (k oneNonzero) (k oneNonzero) = EvenClifford.identity (TernaryForm.lorentz oneNonzero) ∧
    EvenClifford.mul (j oneNonzero) (i oneNonzero) = k oneNonzero ∧
    EvenClifford.mul (j oneNonzero) (k oneNonzero) = i oneNonzero ∧
    EvenClifford.mul (i oneNonzero) (k oneNonzero) = j oneNonzero ∧
    EvenClifford.mul (i oneNonzero) (j oneNonzero) = EvenClifford.scale (-1) (k oneNonzero) ∧
    EvenClifford.mul (k oneNonzero) (j oneNonzero) = EvenClifford.scale (-1) (i oneNonzero) ∧
    EvenClifford.mul (k oneNonzero) (i oneNonzero) = EvenClifford.scale (-1) (j oneNonzero) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply TernaryForm.EvenClifford.ext
  all_goals
    dsimp only [i, j, k, coordinates, EvenClifford.mul, EvenClifford.productScalar,
      EvenClifford.productVector, EvenClifford.identity, EvenClifford.scale]
  all_goals try simp only [TernaryForm.lorentz_determinant, TernaryForm.bilinear_lorentz, -eq_self, -iff_self]
  all_goals try apply Vector3.ext
  all_goals try dsimp only [TernaryForm.cliffordCross]
  all_goals try simp only [TernaryForm.lorentz_adjugate, -eq_self, -iff_self]
  all_goals try dsimp only
    [Vector3.add, Vector3.sub, Vector3.scale, Vector3.neg, Vector3.zero, Vector3.cross, Matrix3.rowMul]
  all_goals ring1

/-- The Clifford norm in dihedron coordinates is `x²+t²-r²-s²`. -/
theorem norm_coordinates (oneNonzero : (1 : K) ≠ 0) (scalar : K) (vector : Vector3 K) :
    EvenClifford.norm (coordinates oneNonzero scalar vector) =
      scalar ^ 2 + vector.t ^ 2 - vector.r ^ 2 - vector.s ^ 2 := by
  unfold EvenClifford.norm
  rw [TernaryForm.lorentz_determinant, TernaryForm.quadrance_lorentz]
  unfold coordinates Vector3.neg
  ring1

/-- Matrix determinant equals the norm of the original Lorentz Clifford value. -/
theorem determinant_toMatrix (oneNonzero : (1 : K) ≠ 0)
    (value : (TernaryForm.lorentz oneNonzero).EvenClifford) :
    Matrix2.determinant (toMatrix oneNonzero value) = EvenClifford.norm value := by
  unfold Matrix2.determinant toMatrix EvenClifford.norm
  rw [TernaryForm.lorentz_determinant, TernaryForm.quadrance_lorentz]
  ring1

/-- Lorentz Clifford conjugation corresponds to matrix adjugation. -/
theorem toMatrix_conjugate (oneNonzero : (1 : K) ≠ 0)
    (value : (TernaryForm.lorentz oneNonzero).EvenClifford) :
    toMatrix oneNonzero (EvenClifford.conjugate value) = Matrix2.adjugate (toMatrix oneNonzero value) := by
  ext <;> unfold toMatrix EvenClifford.conjugate Matrix2.adjugate Vector3.neg <;> ring1

/-- The matrix model preserves Lorentz Clifford multiplication. -/
theorem toMatrix_mul (oneNonzero : (1 : K) ≠ 0)
    (left right : (TernaryForm.lorentz oneNonzero).EvenClifford) :
    toMatrix oneNonzero (EvenClifford.mul left right) =
      Matrix2.mul (toMatrix oneNonzero left) (toMatrix oneNonzero right) := by
  ext <;> unfold toMatrix EvenClifford.mul EvenClifford.productScalar EvenClifford.productVector
    Vector3.sub Vector3.add Vector3.scale TernaryForm.cliffordCross Matrix3.rowMul Vector3.cross
    Matrix2.mul <;>
    rw [TernaryForm.lorentz_determinant, TernaryForm.bilinear_lorentz, TernaryForm.lorentz_adjugate] <;>
    ring1

/-- Decoding after encoding returns the original Lorentz Clifford value.

The nonzero-two certificate justifies the half-sum and half-difference formulas.
-/
theorem fromMatrix_toMatrix (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (value : (TernaryForm.lorentz oneNonzero).EvenClifford) :
    fromMatrix oneNonzero (toMatrix oneNonzero value) = value := by
  have cancel := ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  apply TernaryForm.EvenClifford.ext
  · change (2 : K)⁻¹ * (value.scalar - value.vector.s + (value.scalar + value.vector.s)) = value.scalar
    calc
      _ = value.scalar * ((2 : K) * (2 : K)⁻¹) := by ring1
      _ = value.scalar := by rw [cancel, mul_one]
  · apply Vector3.ext
    · change (2 : K)⁻¹ * (value.vector.t - value.vector.r - (-value.vector.r - value.vector.t)) = value.vector.t
      calc
        _ = value.vector.t * ((2 : K) * (2 : K)⁻¹) := by ring1
        _ = value.vector.t := by rw [cancel, mul_one]
    · change -(2 : K)⁻¹ * (value.vector.t - value.vector.r + (-value.vector.r - value.vector.t)) = value.vector.r
      calc
        _ = value.vector.r * ((2 : K) * (2 : K)⁻¹) := by ring1
        _ = value.vector.r := by rw [cancel, mul_one]
    · change (2 : K)⁻¹ * (value.scalar + value.vector.s - (value.scalar - value.vector.s)) = value.vector.s
      calc
        _ = value.vector.s * ((2 : K) * (2 : K)⁻¹) := by ring1
        _ = value.vector.s := by rw [cancel, mul_one]

/-- Encoding the decoded coordinates returns the supplied matrix. -/
theorem toMatrix_fromMatrix (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (matrix : Matrix2 K) : toMatrix oneNonzero (fromMatrix oneNonzero matrix) = matrix := by
  have cancel := ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  apply Matrix2.ext
  · change (2 : K)⁻¹ * (matrix.a + matrix.d) - (2 : K)⁻¹ * (matrix.d - matrix.a) = matrix.a
    calc
      _ = matrix.a * ((2 : K) * (2 : K)⁻¹) := by ring1
      _ = matrix.a := by rw [cancel, mul_one]
  · change (2 : K)⁻¹ * (matrix.b - matrix.c) - (-(2 : K)⁻¹ * (matrix.b + matrix.c)) = matrix.b
    calc
      _ = matrix.b * ((2 : K) * (2 : K)⁻¹) := by ring1
      _ = matrix.b := by rw [cancel, mul_one]
  · change -(-(2 : K)⁻¹ * (matrix.b + matrix.c)) - (2 : K)⁻¹ * (matrix.b - matrix.c) = matrix.c
    calc
      _ = matrix.c * ((2 : K) * (2 : K)⁻¹) := by ring1
      _ = matrix.c := by rw [cancel, mul_one]
  · change (2 : K)⁻¹ * (matrix.a + matrix.d) + (2 : K)⁻¹ * (matrix.d - matrix.a) = matrix.d
    calc
      _ = matrix.d * ((2 : K) * (2 : K)⁻¹) := by ring1
      _ = matrix.d := by rw [cancel, mul_one]

/-- Equal matrix encodings have equal Lorentz Clifford inputs. -/
theorem toMatrix_injective (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    {left right : (TernaryForm.lorentz oneNonzero).EvenClifford}
    (equal : toMatrix oneNonzero left = toMatrix oneNonzero right) : left = right := by
  calc
    left = fromMatrix oneNonzero (toMatrix oneNonzero left) :=
      (fromMatrix_toMatrix oneNonzero twoNonzero left).symm
    _ = fromMatrix oneNonzero (toMatrix oneNonzero right) := congrArg (fromMatrix oneNonzero) equal
    _ = right := fromMatrix_toMatrix oneNonzero twoNonzero right

/-- A nonzero original Lorentz dihedron has a nonzero two-by-two matrix.

The supplied nonzero two certifies matrix coordinate recovery. If all four
matrix entries were zero, injectivity would identify the original dihedron
with the zero scalar-and-vector record of the same Lorentz form.
-/
theorem toMatrix_nonzero [DecidableEq K] (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (value : (TernaryForm.lorentz oneNonzero).EvenClifford) (nonzero : value ≠ ⟨0, Vector3.zero⟩) :
    (toMatrix oneNonzero value).IsNonzero := by
  apply (Matrix2.isNonzero_iff_ne_zero _).mpr
  intro zeroMatrix
  apply nonzero
  apply toMatrix_injective oneNonzero twoNonzero
  calc
    toMatrix oneNonzero value = ⟨0, 0, 0, 0⟩ := zeroMatrix
    _ = toMatrix oneNonzero ⟨0, Vector3.zero⟩ := by
      apply Matrix2.ext <;> unfold toMatrix Vector3.zero <;> ring1

/-- Factor the exact matrix of a nonzero null Lorentz dihedron into its two original homogeneous spinors.

The dihedron retains its Lorentz-form owner, and the returned factorization
is indexed by its original matrix. Its zero norm supplies singularity, and
matrix coordinate recovery reflects the supplied dihedron nonzeroness.
-/
@[expose] def nullFactorization [DecidableEq K] (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (value : (TernaryForm.lorentz oneNonzero).EvenClifford) (nonzero : value ≠ ⟨0, Vector3.zero⟩)
    (null : EvenClifford.norm value = 0) : Matrix2.RankOneFactorization (toMatrix oneNonzero value) :=
  Matrix2.rankOneFactorization (toMatrix oneNonzero value) oneNonzero
    (toMatrix_nonzero oneNonzero twoNonzero value nonzero) ((determinant_toMatrix oneNonzero value).trans null)

/-- The original non-null dihedron matrix is an invertible representative with the same retained entries. -/
@[expose] def toInvertible (oneNonzero : (1 : K) ≠ 0)
    (value : (TernaryForm.lorentz oneNonzero).NonNullEvenClifford) : Matrix2.Invertible K where
  matrix := toMatrix oneNonzero value.toEvenClifford
  determinantNonzero := by rw [determinant_toMatrix]; exact value.normNonzero

/-- Decode an invertible matrix into the original non-null Lorentz Clifford owner.

The original half-sum coordinate decoder computes the parent. The matrix's
retained nonzero determinant certifies its norm using the same matrix
reconstruction equation; no new representative or normalization is chosen.
-/
@[expose] def fromInvertible (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (value : Matrix2.Invertible K) : (TernaryForm.lorentz oneNonzero).NonNullEvenClifford :=
  let decoded := fromMatrix oneNonzero value.matrix
  { toEvenClifford := decoded
    normNonzero := by
      have norm : EvenClifford.norm decoded = value.matrix.determinant := by
        calc
          EvenClifford.norm decoded = (toMatrix oneNonzero decoded).determinant :=
            (determinant_toMatrix oneNonzero decoded).symm
          _ = value.matrix.determinant :=
            congrArg Matrix2.determinant (toMatrix_fromMatrix oneNonzero twoNonzero value.matrix)
      rw [norm]
      exact value.determinantNonzero }

/-- Decoding the invertible matrix of an original non-null dihedron returns that same original record. -/
theorem fromInvertible_toInvertible (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (value : (TernaryForm.lorentz oneNonzero).NonNullEvenClifford) :
    fromInvertible oneNonzero twoNonzero (toInvertible oneNonzero value) = value := by
  have coordinates := fromMatrix_toMatrix oneNonzero twoNonzero value.toEvenClifford
  apply TernaryForm.NonNullEvenClifford.ext
  · exact congrArg TernaryForm.EvenClifford.scalar coordinates
  · exact congrArg TernaryForm.EvenClifford.vector coordinates

/-- Encoding the decoded non-null dihedron returns the original invertible matrix record. -/
theorem toInvertible_fromInvertible (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (value : Matrix2.Invertible K) :
    toInvertible oneNonzero (fromInvertible oneNonzero twoNonzero value) = value :=
  Matrix2.Invertible.eq_of_matrix_eq (toMatrix_fromMatrix oneNonzero twoNonzero value.matrix)

/-- Equality of the invertible matrices reflects equality of the two original non-null dihedrons. -/
theorem toInvertible_injective (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    {left right : (TernaryForm.lorentz oneNonzero).NonNullEvenClifford}
    (equal : toInvertible oneNonzero left = toInvertible oneNonzero right) : left = right := by
  have coordinates := toMatrix_injective oneNonzero twoNonzero (congrArg Matrix2.Invertible.matrix equal)
  apply TernaryForm.NonNullEvenClifford.ext
  · exact congrArg TernaryForm.EvenClifford.scalar coordinates
  · exact congrArg TernaryForm.EvenClifford.vector coordinates

/-- The non-null dihedron matrix correspondence preserves multiplication of the original two input owners. -/
theorem toInvertible_mul (oneNonzero : (1 : K) ≠ 0)
    (left right : (TernaryForm.lorentz oneNonzero).NonNullEvenClifford) :
    toInvertible oneNonzero (NonNullEvenClifford.mul left right) =
      Matrix2.Invertible.mul (toInvertible oneNonzero left) (toInvertible oneNonzero right) :=
  Matrix2.Invertible.eq_of_matrix_eq (toMatrix_mul oneNonzero left.toEvenClifford right.toEvenClifford)

/-- Decoding multiplication of invertible matrices preserves the original non-null dihedron product. -/
theorem fromInvertible_mul (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (left right : Matrix2.Invertible K) :
    fromInvertible oneNonzero twoNonzero (Matrix2.Invertible.mul left right) =
      NonNullEvenClifford.mul (fromInvertible oneNonzero twoNonzero left)
        (fromInvertible oneNonzero twoNonzero right) := by
  apply toInvertible_injective oneNonzero twoNonzero
  rw [toInvertible_fromInvertible, toInvertible_mul, toInvertible_fromInvertible, toInvertible_fromInvertible]

/-- The dihedron matrix correspondence preserves and reflects the exact nonzero projective-scale relation.

Both input dihedrons keep their original Lorentz Clifford parents. The same
supplied scalar scales their matrices; coordinate recovery reflects matrix
equality to parent equality without replacing that witness.
-/
theorem toInvertible_equivalent_iff (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (left right : (TernaryForm.lorentz oneNonzero).NonNullEvenClifford) :
    (toInvertible oneNonzero left).Equivalent (toInvertible oneNonzero right) ↔
      NonNullEvenClifford.Equivalent left right := by
  constructor
  · rintro ⟨factor, nonzero, represents⟩
    refine ⟨factor, nonzero, ?_⟩
    apply toMatrix_injective oneNonzero twoNonzero
    calc
      toMatrix oneNonzero right.toEvenClifford = Matrix2.scalarScale factor
          (toMatrix oneNonzero left.toEvenClifford) := represents
      _ = toMatrix oneNonzero (EvenClifford.scale factor left.toEvenClifford) :=
        (toMatrix_scale oneNonzero factor left.toEvenClifford).symm
  · rintro ⟨factor, nonzero, represents⟩
    refine ⟨factor, nonzero, ?_⟩
    calc
      toMatrix oneNonzero right.toEvenClifford =
          toMatrix oneNonzero (EvenClifford.scale factor left.toEvenClifford) :=
        congrArg (toMatrix oneNonzero) represents
      _ = Matrix2.scalarScale factor (toMatrix oneNonzero left.toEvenClifford) :=
        toMatrix_scale oneNonzero factor left.toEvenClifford

/-- Decoding preserves and reflects the original invertible matrices' projective scale relation. -/
theorem fromInvertible_equivalent_iff (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (left right : Matrix2.Invertible K) :
    NonNullEvenClifford.Equivalent (fromInvertible oneNonzero twoNonzero left)
        (fromInvertible oneNonzero twoNonzero right) ↔ left.Equivalent right := by
  have correspondence := (toInvertible_equivalent_iff oneNonzero twoNonzero
    (fromInvertible oneNonzero twoNonzero left) (fromInvertible oneNonzero twoNonzero right)).symm
  rw [toInvertible_fromInvertible, toInvertible_fromInvertible] at correspondence
  exact correspondence

end Purelib.Algebra.Clifford.Lorentz.Matrix
