module

public import Purelib.Algebra.Clifford.Ternary.Action
import Purelib.Algebra.Clifford.Ternary.Basic
import Purelib.Algebra.Quadratic.Ternary.Basic
public import Purelib.Algebra.Quadratic.Ternary.Minkowski
public import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

@[expose] public section

namespace Purelib.Algebra.Clifford.Split.Matrix.MinkowskiClifford

open Purelib.Algebra.Field (ExplicitField)
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm

variable {K : Type*} [ExplicitField K]

/-- Recover split Clifford coordinates from a displayed two-by-two matrix.

Half-sums and half-differences recover the scalar and three vector coordinates; the inverse identities additionally
require two to be nonzero. -/
def fromMatrix (oneNonzero : (1 : K) ≠ 0) (matrix :
  Matrix2 K) :
    (Form.minkowski oneNonzero).EvenClifford :=
  ⟨(2 : K)⁻¹ * (matrix.a + matrix.d),
    ⟨(2 : K)⁻¹ * (matrix.a - matrix.d),
      (2 : K)⁻¹ * (matrix.b + matrix.c),
      (2 : K)⁻¹ * (matrix.c - matrix.b)⟩⟩

/-- Encode a split Clifford representative as a displayed two-by-two matrix.

The entries are the scalar plus or minus the first vector coordinate and the two signed sums of the remaining
coordinates. -/
def toMatrix (oneNonzero : (1 : K) ≠ 0)
    (value : (Form.minkowski oneNonzero).EvenClifford) : Matrix2 K :=
  ⟨value.scalar + value.vector.t,
    value.vector.r - value.vector.s,
    value.vector.r + value.vector.s,
    value.scalar - value.vector.t⟩

/-- Matrix determinant is precisely the split Clifford reduced norm. -/
theorem determinant_toMatrix (oneNonzero : (1 : K) ≠ 0)
    (value : (Form.minkowski oneNonzero).EvenClifford) :
    Matrix2.determinant (MinkowskiClifford.toMatrix oneNonzero value) = (EvenClifford.norm value) := by
  unfold Matrix2.determinant MinkowskiClifford.toMatrix EvenClifford.norm
  rw [Form.minkowski_determinant,
    Form.quadrance_minkowski]
  ring1

/-- Recovering coordinates after matrix encoding returns the original split Clifford representative.

The supplied nonzero-two certificate justifies the half-sum reconstruction. -/
theorem fromMatrix_toMatrix (oneNonzero : (1 : K) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (value : (Form.minkowski oneNonzero).EvenClifford) :
    MinkowskiClifford.fromMatrix oneNonzero (MinkowskiClifford.toMatrix oneNonzero value) = value := by
  have cancel := ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  have reverseCancel : (2 : K)⁻¹ * 2 = 1 := by
    calc
      (2 : K)⁻¹ * 2 = 2 * (2 : K)⁻¹ := by ring1
      _ = 1 := cancel
  have halfDouble (entry : K) :
      (2 : K)⁻¹ * (entry + entry) = entry := by
    calc
      (2 : K)⁻¹ * (entry + entry) =
          ((2 : K)⁻¹ * 2) * entry := by ring1
      _ = entry := by rw [reverseCancel, one_mul]
  apply Form.EvenClifford.ext
  · unfold MinkowskiClifford.fromMatrix MinkowskiClifford.toMatrix
    calc
      (2 : K)⁻¹ *
          ((value.scalar + value.vector.t) +
            (value.scalar - value.vector.t)) =
        (2 : K)⁻¹ * (value.scalar + value.scalar) := by ring1
      _ = value.scalar := halfDouble value.scalar
  · apply Vector3.ext
    · unfold MinkowskiClifford.fromMatrix MinkowskiClifford.toMatrix
      calc
        (2 : K)⁻¹ *
            ((value.scalar + value.vector.t) -
              (value.scalar - value.vector.t)) =
          (2 : K)⁻¹ * (value.vector.t + value.vector.t) := by ring1
        _ = value.vector.t := halfDouble value.vector.t
    · unfold MinkowskiClifford.fromMatrix MinkowskiClifford.toMatrix
      calc
        (2 : K)⁻¹ *
            ((value.vector.r - value.vector.s) +
              (value.vector.r + value.vector.s)) =
          (2 : K)⁻¹ * (value.vector.r + value.vector.r) := by ring1
        _ = value.vector.r := halfDouble value.vector.r
    · unfold MinkowskiClifford.fromMatrix MinkowskiClifford.toMatrix
      calc
        (2 : K)⁻¹ *
            ((value.vector.r + value.vector.s) -
              (value.vector.r - value.vector.s)) =
          (2 : K)⁻¹ * (value.vector.s + value.vector.s) := by ring1
        _ = value.vector.s := halfDouble value.vector.s

/-- Clifford conjugation becomes the ordinary two-by-two adjugate. -/
theorem toMatrix_conjugate (oneNonzero : (1 : K) ≠ 0)
    (value : (Form.minkowski oneNonzero).EvenClifford) :
    MinkowskiClifford.toMatrix oneNonzero (EvenClifford.conjugate value) =
      Matrix2.adjugate (MinkowskiClifford.toMatrix oneNonzero value) := by
  ext <;> unfold MinkowskiClifford.toMatrix EvenClifford.conjugate
    Matrix2.adjugate Vector3.neg <;> ring1

/-- Encoding the recovered split Clifford coordinates returns the original matrix.

The supplied nonzero-two certificate justifies the half-sum reconstruction. -/
theorem toMatrix_fromMatrix (oneNonzero : (1 : K) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) (matrix : Matrix2 K) :
    MinkowskiClifford.toMatrix oneNonzero (MinkowskiClifford.fromMatrix oneNonzero matrix) = matrix := by
  have cancel := ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  have reverseCancel : (2 : K)⁻¹ * 2 = 1 := by
    calc
      (2 : K)⁻¹ * 2 = 2 * (2 : K)⁻¹ := by ring1
      _ = 1 := cancel
  have halfDouble (entry : K) :
      (2 : K)⁻¹ * (entry + entry) = entry := by
    calc
      (2 : K)⁻¹ * (entry + entry) =
          ((2 : K)⁻¹ * 2) * entry := by ring1
      _ = entry := by rw [reverseCancel, one_mul]
  apply Matrix2.ext
  · unfold MinkowskiClifford.toMatrix MinkowskiClifford.fromMatrix
    calc
      (2 : K)⁻¹ * (matrix.a + matrix.d) +
          (2 : K)⁻¹ * (matrix.a - matrix.d) =
        (2 : K)⁻¹ * (matrix.a + matrix.a) := by ring1
      _ = matrix.a := halfDouble matrix.a
  · unfold MinkowskiClifford.toMatrix MinkowskiClifford.fromMatrix
    calc
      (2 : K)⁻¹ * (matrix.b + matrix.c) -
          (2 : K)⁻¹ * (matrix.c - matrix.b) =
        (2 : K)⁻¹ * (matrix.b + matrix.b) := by ring1
      _ = matrix.b := halfDouble matrix.b
  · unfold MinkowskiClifford.toMatrix MinkowskiClifford.fromMatrix
    calc
      (2 : K)⁻¹ * (matrix.b + matrix.c) +
          (2 : K)⁻¹ * (matrix.c - matrix.b) =
        (2 : K)⁻¹ * (matrix.c + matrix.c) := by ring1
      _ = matrix.c := halfDouble matrix.c
  · unfold MinkowskiClifford.toMatrix MinkowskiClifford.fromMatrix
    calc
      (2 : K)⁻¹ * (matrix.a + matrix.d) -
          (2 : K)⁻¹ * (matrix.a - matrix.d) =
        (2 : K)⁻¹ * (matrix.d + matrix.d) := by ring1
      _ = matrix.d := halfDouble matrix.d

/-- The split Clifford matrix encoding is injective when two is nonzero. -/
theorem toMatrix_injective (oneNonzero : (1 : K) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    {left right : (Form.minkowski oneNonzero).EvenClifford}
    (equal : MinkowskiClifford.toMatrix oneNonzero left = MinkowskiClifford.toMatrix oneNonzero right) :
    left = right := by
  have mapped := congrArg (MinkowskiClifford.fromMatrix oneNonzero) equal
  rw [MinkowskiClifford.fromMatrix_toMatrix oneNonzero twoNonzero,
    MinkowskiClifford.fromMatrix_toMatrix oneNonzero twoNonzero] at mapped
  exact mapped

/-- The split coordinate map preserves multiplication exactly. -/
theorem toMatrix_mul (oneNonzero : (1 : K) ≠ 0)
    (left right : (Form.minkowski oneNonzero).EvenClifford) :
    MinkowskiClifford.toMatrix oneNonzero (EvenClifford.mul left right) =
      Matrix2.mul (MinkowskiClifford.toMatrix oneNonzero left) (MinkowskiClifford.toMatrix oneNonzero right) := by
  ext <;> unfold MinkowskiClifford.toMatrix Matrix2.mul EvenClifford.mul
    EvenClifford.productScalar
    EvenClifford.productVector Form.cliffordCross
    Form.bilinear Form.minkowski Form.ofMatrix
    Matrix3.adjugate Matrix3.determinant Matrix3.rowMul Vector3.dot
    Vector3.cross Vector3.add Vector3.sub Vector3.scale <;> ring1

/-- Trace-zero matrix corresponding to a Minkowski vector. -/
def vectorMatrix (vector : Vector3 K) : Matrix2 K :=
  ⟨vector.t, vector.r - vector.s,
    vector.r + vector.s, -vector.t⟩

set_option genInjectivity false in
/-- Retain the executable split Clifford and two-by-two matrix correspondence.

The forward and backward maps carry inverse identities, multiplication and norm compatibility, conjugation as
adjugation, and the normalized vector-action formula. -/
structure AlgebraEquivalence (oneNonzero : (1 : K) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) where
  /-- The retained map from split Clifford representatives to displayed matrices. -/ forward : (Form.minkowski
    oneNonzero).EvenClifford → Matrix2 K
  /-- The retained map recovering split Clifford representatives from matrices. -/ backward : Matrix2 K →
    (Form.minkowski oneNonzero).EvenClifford
  /-- Matrix encoding after coordinate recovery is the identity. -/ forward_backward : ∀ matrix : Matrix2 K,
    forward (backward matrix) = matrix
  /-- Coordinate recovery after matrix encoding is the identity. -/ backward_forward : ∀ value :
      (Form.minkowski oneNonzero).EvenClifford,
    backward (forward value) = value
  /-- The forward map preserves the displayed Clifford and matrix products. -/ map_mul : ∀ left right :
      (Form.minkowski oneNonzero).EvenClifford,
    forward (EvenClifford.mul left right) =
      Matrix2.mul (forward left) (forward right)
  /-- Matrix determinant of the image equals the original reduced Clifford norm. -/ map_determinant : ∀ value :
      (Form.minkowski oneNonzero).EvenClifford,
    Matrix2.determinant (forward value) = (EvenClifford.norm value)
  /-- The forward map sends Clifford conjugation to matrix adjugation. -/ map_conjugate : ∀ value :
      (Form.minkowski oneNonzero).EvenClifford,
    forward (EvenClifford.conjugate value) = Matrix2.adjugate (forward value)
  /-- The normalized vector action is the adjugate sandwich divided by the original nonzero reduced norm. -/
    normalizedAction : ∀
      (value : (Form.minkowski oneNonzero).NonNullEvenClifford)
      (vector : Vector3 K),
    MinkowskiClifford.vectorMatrix ((NonNullEvenClifford.action value vector)) =
      Matrix2.scalarScale (EvenClifford.norm value.toEvenClifford)⁻¹
        (Matrix2.mul
          (Matrix2.mul
            (Matrix2.adjugate (forward value.toEvenClifford))
            (MinkowskiClifford.vectorMatrix vector))
          (forward value.toEvenClifford))

constructive_injectivity AlgebraEquivalence

/-- A pure Clifford vector encodes as its displayed trace-zero matrix. -/
theorem toMatrix_ofVector (oneNonzero : (1 : K) ≠ 0)
    (vector : Vector3 K) :
    MinkowskiClifford.toMatrix oneNonzero
        (EvenClifford.ofVector
          (Form.minkowski oneNonzero) vector) =
      MinkowskiClifford.vectorMatrix vector := by
  ext <;> unfold MinkowskiClifford.toMatrix EvenClifford.ofVector MinkowskiClifford.vectorMatrix <;>
    ring1

/-- The Clifford action is the adjugate sandwich on trace-zero matrices. -/
theorem actionNumerator_compatibility (oneNonzero : (1 :
  K) ≠ 0)
    (value : (Form.minkowski oneNonzero).EvenClifford)
    (vector : Vector3 K) :
    MinkowskiClifford.vectorMatrix ((EvenClifford.actionNumerator value) vector) =
      Matrix2.mul
        (Matrix2.mul
          (Matrix2.adjugate (MinkowskiClifford.toMatrix oneNonzero value))
          (MinkowskiClifford.vectorMatrix vector))
        (MinkowskiClifford.toMatrix oneNonzero value) := by
  calc
    MinkowskiClifford.vectorMatrix ((EvenClifford.actionNumerator value) vector) =
        MinkowskiClifford.toMatrix oneNonzero
          (EvenClifford.ofVector
            (Form.minkowski oneNonzero)
            ((EvenClifford.actionNumerator value) vector)) :=
      (MinkowskiClifford.toMatrix_ofVector oneNonzero ((EvenClifford.actionNumerator value) vector)).symm
    _ = MinkowskiClifford.toMatrix oneNonzero
        (EvenClifford.mul
          (EvenClifford.mul (EvenClifford.conjugate value)
            (EvenClifford.ofVector
              (Form.minkowski oneNonzero) vector))
          value) := by
      rw [EvenClifford.conjugate_mul_ofVector_mul]
    _ = Matrix2.mul
        (Matrix2.mul
          (MinkowskiClifford.toMatrix oneNonzero (EvenClifford.conjugate value))
          (MinkowskiClifford.toMatrix oneNonzero
            (EvenClifford.ofVector
              (Form.minkowski oneNonzero) vector)))
        (MinkowskiClifford.toMatrix oneNonzero value) := by
      rw [MinkowskiClifford.toMatrix_mul, MinkowskiClifford.toMatrix_mul]
    _ = Matrix2.mul
        (Matrix2.mul
          (Matrix2.adjugate (MinkowskiClifford.toMatrix oneNonzero value))
          (MinkowskiClifford.vectorMatrix vector))
        (MinkowskiClifford.toMatrix oneNonzero value) := by
      rw [MinkowskiClifford.toMatrix_conjugate, MinkowskiClifford.toMatrix_ofVector]

/-- Scaling a displayed vector scales its trace-zero matrix by the same factor. -/
theorem vectorMatrix_scale (factor : K) (vector : Vector3
  K) :
    MinkowskiClifford.vectorMatrix (Vector3.scale factor vector) =
      Matrix2.scalarScale factor (MinkowskiClifford.vectorMatrix vector) := by
  ext <;> unfold MinkowskiClifford.vectorMatrix Matrix2.scalarScale Vector3.scale <;> ring1

/-- The normalized special-orthogonal action is the determinant-normalized
two-by-two adjugate sandwich. -/
theorem action_compatibility (oneNonzero : (1 : K) ≠ 0)
    (value : (Form.minkowski oneNonzero).NonNullEvenClifford)
    (vector : Vector3 K) :
    MinkowskiClifford.vectorMatrix ((NonNullEvenClifford.action value vector)) =
      Matrix2.scalarScale (EvenClifford.norm value.toEvenClifford)⁻¹
        (Matrix2.mul
          (Matrix2.mul
            (Matrix2.adjugate
              (MinkowskiClifford.toMatrix oneNonzero value.toEvenClifford))
            (MinkowskiClifford.vectorMatrix vector))
          (MinkowskiClifford.toMatrix oneNonzero value.toEvenClifford)) := by
  unfold NonNullEvenClifford.action
  rw [MinkowskiClifford.vectorMatrix_scale,
    MinkowskiClifford.actionNumerator_compatibility]

/-- Assemble the canonical split Clifford matrix correspondence and its certificates.

The nonzero-one certificate defines the retained Minkowski form, and nonzero two certifies the half-sum inverse
coordinate map. -/
def algebraEquivalence (oneNonzero : (1 : K) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    MinkowskiClifford.AlgebraEquivalence oneNonzero twoNonzero where
  forward := MinkowskiClifford.toMatrix oneNonzero
  backward := MinkowskiClifford.fromMatrix oneNonzero
  forward_backward := MinkowskiClifford.toMatrix_fromMatrix oneNonzero twoNonzero
  backward_forward := MinkowskiClifford.fromMatrix_toMatrix oneNonzero twoNonzero
  map_mul := MinkowskiClifford.toMatrix_mul oneNonzero
  map_determinant := MinkowskiClifford.determinant_toMatrix oneNonzero
  map_conjugate := MinkowskiClifford.toMatrix_conjugate oneNonzero
  normalizedAction := MinkowskiClifford.action_compatibility oneNonzero

end Purelib.Algebra.Clifford.Split.Matrix.MinkowskiClifford
