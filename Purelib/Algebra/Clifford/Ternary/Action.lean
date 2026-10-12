module
public import Purelib.Algebra.Clifford.Ternary.Basic
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Geometry.Quadratic.Ternary.Isometry
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Quadratic.Ternary.Basic
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring

/-!
# Explicit even Clifford algebra of a ternary form

The four coordinates are stored as one scalar and one displayed vector.  The
product uses the cached adjugate of the form matrix, so it is polynomial in
the supplied finite data and performs no fresh matrix inversion.
-/

@[expose] public section
namespace Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm

open Purelib.LinearAlgebra.Coordinates3 (Matrix3)
open Purelib.Algebra.Field
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K]

namespace EvenClifford

/-- Compute the denominator-cleared conjugation action on a displayed vector.

The formula combines the scalar square, vector quadrance, mixed pairing and adjugate cross, reusing the indexed form
data. -/
def actionNumerator {form : Form K} (value :
  form.EvenClifford)
    (vector : Vector3 K) : Vector3 K :=
  Vector3.add
    (Vector3.add
      (Vector3.scale
        (value.scalar ^ 2 -
          form.determinant * form.quadrance value.vector)
        vector)
      (Vector3.scale
        (2 * form.determinant * form.bilinear vector value.vector)
        value.vector))
    (Vector3.scale (-2 * value.scalar)
      (form.cliffordCross vector value.vector))

/-- The denominator-cleared action is Clifford conjugation of a pure vector,
with no quotient or chosen basis. -/
theorem conjugate_mul_ofVector_mul {form : Form
  K}
    (value : form.EvenClifford) (vector : Vector3 K) :
    EvenClifford.mul (EvenClifford.mul (EvenClifford.conjugate value) (EvenClifford.ofVector form vector)) value =
      EvenClifford.ofVector form ((EvenClifford.actionNumerator value) vector) := by
  apply Form.EvenClifford.ext
  · simp only [EvenClifford.mul, EvenClifford.conjugate, EvenClifford.ofVector, EvenClifford.productScalar,
      EvenClifford.productVector]
    rw [form.bilinear_neg_left, mul_zero,
      Vector3.zero_scale, Vector3.add_zero,
      form.cliffordCross_neg_left,
      form.bilinear_sub_left, form.bilinear_scale_left,
      form.bilinear_neg_left,
      form.bilinear_comm vector value.vector]
    have crossPerpendicular :=
      form.cliffordCross_perpendicular_left value.vector vector
    unfold Form.Perpendicular at crossPerpendicular
    rw [crossPerpendicular]
    ring1
  · simp only [EvenClifford.mul, EvenClifford.conjugate, EvenClifford.ofVector, EvenClifford.productScalar,
      EvenClifford.productVector]
    rw [form.bilinear_neg_left, mul_zero,
      Vector3.zero_scale, Vector3.add_zero,
      form.cliffordCross_neg_left,
      form.cliffordCross_sub_left,
      form.cliffordCross_scale_left,
      form.cliffordCross_neg_left,
      form.cliffordCross_left_triple,
      form.bilinear_comm value.vector vector,
      form.cliffordCross_anticomm value.vector vector]
    ext <;> unfold EvenClifford.actionNumerator Vector3.add Vector3.sub Vector3.scale
      Vector3.neg Form.quadrance <;> ring1

/-- The denominator-cleared action respects Clifford multiplication.  The
order agrees with row-vector matrix multiplication: `left` acts first. -/
theorem actionNumerator_mul {form : Form K}
    (left right : form.EvenClifford) (vector : Vector3 K) :
    (EvenClifford.actionNumerator (EvenClifford.mul left right)) vector =
      (EvenClifford.actionNumerator right) ((EvenClifford.actionNumerator left) vector) := by
  have pureEquality :
      EvenClifford.ofVector form ((EvenClifford.actionNumerator (EvenClifford.mul left right)) vector) =
        EvenClifford.ofVector form
          ((EvenClifford.actionNumerator right) ((EvenClifford.actionNumerator left) vector)) := by
    calc
      EvenClifford.ofVector form ((EvenClifford.actionNumerator (EvenClifford.mul left right)) vector) =
          EvenClifford.mul
            (EvenClifford.mul (EvenClifford.conjugate (EvenClifford.mul left right)) (EvenClifford.ofVector form
              vector))
            (EvenClifford.mul left right) :=
        (EvenClifford.conjugate_mul_ofVector_mul (EvenClifford.mul left right) vector).symm
      _ = EvenClifford.mul
          (EvenClifford.mul (EvenClifford.mul (EvenClifford.conjugate right) (EvenClifford.conjugate left))
            (EvenClifford.ofVector form vector))
          (EvenClifford.mul left right) := by
        rw [EvenClifford.conjugate_mul_reverse]
      _ = EvenClifford.mul
          (EvenClifford.mul (EvenClifford.conjugate right)
            (EvenClifford.mul (EvenClifford.mul (EvenClifford.conjugate left) (EvenClifford.ofVector form vector))
              left))
          right := by
        rw [EvenClifford.mul_assoc (EvenClifford.conjugate right) (EvenClifford.conjugate left),
          ← EvenClifford.mul_assoc
            (EvenClifford.mul (EvenClifford.conjugate right)
              (EvenClifford.mul (EvenClifford.conjugate left) (EvenClifford.ofVector form vector)))
            left right,
          EvenClifford.mul_assoc (EvenClifford.conjugate right)
            (EvenClifford.mul (EvenClifford.conjugate left) (EvenClifford.ofVector form vector)) left]
      _ = EvenClifford.mul
          (EvenClifford.mul (EvenClifford.conjugate right)
            (EvenClifford.ofVector form ((EvenClifford.actionNumerator left) vector)))
          right := by
        rw [EvenClifford.conjugate_mul_ofVector_mul]
      _ = EvenClifford.ofVector form
          ((EvenClifford.actionNumerator right) ((EvenClifford.actionNumerator left) vector)) :=
        EvenClifford.conjugate_mul_ofVector_mul right ((EvenClifford.actionNumerator left) vector)
  exact congrArg Form.EvenClifford.vector pureEquality

/-- The denominator-cleared Clifford action commutes with scaling its vector input. -/
theorem actionNumerator_scale_vector {form : Form
  K}
    (value : form.EvenClifford) (factor : K) (vector : Vector3 K) :
    (EvenClifford.actionNumerator value) (Vector3.scale factor vector) =
      Vector3.scale factor ((EvenClifford.actionNumerator value) vector) := by
  unfold EvenClifford.actionNumerator
  rw [form.bilinear_scale_left,
    form.cliffordCross_scale_left]
  ext <;> unfold Vector3.add Vector3.scale <;> ring1

/-- The vector part of a Clifford value is multiplied by its norm under the action numerator. -/
theorem actionNumerator_vector {form : Form K} (value : form.EvenClifford) :
    actionNumerator value value.vector = Vector3.scale (norm value) value.vector := by
  unfold actionNumerator norm
  rw [form.cliffordCross_self]
  ext <;> unfold Vector3.add Vector3.scale Vector3.zero Form.quadrance <;> ring1

/-- A scalar Clifford value multiplies every vector by its norm under the action numerator. -/
theorem actionNumerator_of_vector_eq_zero {form : Form K} (value : form.EvenClifford)
    (vectorZero : value.vector = Vector3.zero) (vector : Vector3 K) :
    actionNumerator value vector = Vector3.scale (norm value) vector := by
  unfold actionNumerator norm
  rw [vectorZero, form.quadrance_zero, form.bilinear_zero_right, form.cliffordCross_zero_right]
  ext <;> unfold Vector3.add Vector3.scale Vector3.zero <;> ring1

/-- Displayed matrix of the denominator-cleared Clifford action. -/
def actionNumeratorMatrix {form : Form K}
    (value : form.EvenClifford) : Matrix3 K :=
  Matrix3.add
    (Matrix3.add
      (Matrix3.scale
        (value.scalar ^ 2 -
          form.determinant * form.quadrance value.vector)
        Matrix3.identity)
      (Matrix3.scale (2 * form.determinant)
        (Matrix3.outer (form.dual value.vector) value.vector)))
    (Matrix3.scale (2 * value.scalar)
      (form.actionSkew value.vector))

/-- Row multiplication by the displayed action matrix computes the denominator-cleared Clifford action. -/
theorem rowMul_actionNumeratorMatrix {form : Form
  K}
    (value : form.EvenClifford) (vector : Vector3 K) :
    Matrix3.rowMul vector (EvenClifford.actionNumeratorMatrix value) =
      (EvenClifford.actionNumerator value) vector := by
  unfold EvenClifford.actionNumeratorMatrix EvenClifford.actionNumerator
  rw [Matrix3.rowMul_add, Matrix3.rowMul_add,
    Matrix3.rowMul_scale, Matrix3.rowMul_identity,
    Matrix3.rowMul_scale, Matrix3.rowMul_outer,
    ← form.bilinear_eq_dot_dual,
    Matrix3.rowMul_scale, form.rowMul_actionSkew]
  change Vector3.add
    (Vector3.add
      (Vector3.scale
        (value.scalar ^ 2 -
          form.determinant * form.quadrance value.vector) vector)
      (Vector3.scale (2 * form.determinant)
        (Vector3.scale (form.bilinear vector value.vector) value.vector)))
    (Vector3.scale (2 * value.scalar)
      (form.cliffordCross value.vector vector)) = _
  rw [form.cliffordCross_anticomm value.vector vector]
  ext <;> unfold Vector3.add Vector3.scale Vector3.neg <;> ring1

/-- The action numerator is a quadratic polynomial in its relative skew
matrix. -/
theorem actionNumeratorMatrix_eq_quadratic {form
  : Form K}
    (value : form.EvenClifford) :
    (EvenClifford.actionNumeratorMatrix value) =
      Matrix3.add
        (Matrix3.add
          (Matrix3.scale (EvenClifford.norm value) Matrix3.identity)
          (Matrix3.scale (2 * value.scalar)
            (form.actionSkew value.vector)))
        (Matrix3.scale 2
          (Matrix3.mul (form.actionSkew value.vector)
            (form.actionSkew value.vector))) := by
  rw [form.actionSkew_square]
  ext <;> unfold EvenClifford.actionNumeratorMatrix EvenClifford.norm Matrix3.add Matrix3.sub
    Matrix3.scale Matrix3.identity <;> ring1

/-- Orientation calculation for the denominator-cleared action. -/
theorem determinant_actionNumeratorMatrix {form :
  Form K}
    (value : form.EvenClifford) :
    Matrix3.determinant (EvenClifford.actionNumeratorMatrix value) = (EvenClifford.norm value) ^ 3 := by
  rw [(EvenClifford.actionNumeratorMatrix_eq_quadratic value),
    Matrix3.determinant_quadratic_polynomial,
    form.trace_actionSkew,
    form.principalTrace_actionSkew,
    form.determinant_actionSkew]
  unfold EvenClifford.norm
  ring1

/-- Scaling the Clifford representative multiplies its action numerator by the square of the factor. -/
theorem actionNumerator_scale {form : Form K}
  (factor : K)
    (value : form.EvenClifford) (vector : Vector3 K) :
    EvenClifford.actionNumerator (EvenClifford.scale factor value) vector =
      Vector3.scale (factor ^ 2) (EvenClifford.actionNumerator value vector) := by
  unfold EvenClifford.actionNumerator EvenClifford.scale
  rw [form.quadrance_scale, form.bilinear_scale_right,
    form.cliffordCross_scale_right]
  ext <;> unfold Vector3.add Vector3.scale <;> ring1

/-- The Clifford identity acts as the identity on displayed vectors. -/
@[simp] theorem actionNumerator_identity (form :
  Form K)
    (vector : Vector3 K) :
    EvenClifford.actionNumerator (EvenClifford.identity form) vector = vector := by
  ext <;> unfold EvenClifford.actionNumerator EvenClifford.identity Vector3.add Vector3.scale Vector3.zero
    Form.quadrance Form.bilinear Form.cliffordCross Matrix3.rowMul Vector3.dot Vector3.cross <;>
    ring1

/-- The denominator-cleared Clifford action scales quadrance by the square of
the reduced norm. -/
theorem quadrance_actionNumerator {form : Form K}
    (value : form.EvenClifford) (vector : Vector3 K) :
    form.quadrance (EvenClifford.actionNumerator value vector) =
      (EvenClifford.norm value) ^ 2 * form.quadrance vector := by
  have vectorCross :
      form.bilinear vector
          (form.cliffordCross vector value.vector) = 0 := by
    rw [form.bilinear_comm]
    exact form.cliffordCross_perpendicular_left vector value.vector
  have valueCross :
      form.bilinear value.vector
          (form.cliffordCross vector value.vector) = 0 := by
    rw [form.bilinear_comm]
    exact form.cliffordCross_perpendicular_right vector value.vector
  have mixedCross :
      form.bilinear
          (Vector3.add
            (Vector3.scale
              (value.scalar ^ 2 -
                form.determinant * form.quadrance value.vector)
              vector)
            (Vector3.scale
              (2 * form.determinant *
                form.bilinear vector value.vector)
              value.vector))
          (Vector3.scale (-2 * value.scalar)
            (form.cliffordCross vector value.vector)) = 0 := by
    rw [form.bilinear_add_left, form.bilinear_scale_left,
      form.bilinear_scale_right, vectorCross,
      form.bilinear_scale_left, form.bilinear_scale_right, valueCross]
    ring1
  have mainQuadrance :
      form.quadrance
          (Vector3.add
            (Vector3.scale
              (value.scalar ^ 2 -
                form.determinant * form.quadrance value.vector)
              vector)
            (Vector3.scale
              (2 * form.determinant *
                form.bilinear vector value.vector)
              value.vector)) =
        (value.scalar ^ 2 -
            form.determinant * form.quadrance value.vector) ^ 2 *
            form.quadrance vector +
          2 *
            (value.scalar ^ 2 -
              form.determinant * form.quadrance value.vector) *
            (2 * form.determinant *
              form.bilinear vector value.vector) *
            form.bilinear vector value.vector +
          (2 * form.determinant *
              form.bilinear vector value.vector) ^ 2 *
            form.quadrance value.vector := by
    rw [form.quadrance_add, form.quadrance_scale,
      form.quadrance_scale, form.bilinear_scale_left,
      form.bilinear_scale_right]
    ring1
  unfold EvenClifford.actionNumerator
  rw [form.quadrance_add, mixedCross, mainQuadrance,
    form.quadrance_scale, form.quadrance_cliffordCross]
  unfold EvenClifford.norm
  ring1

/-- The denominator-cleared action scales the full bilinear form by the square
of the reduced norm, without using polarization or a characteristic
assumption. -/
theorem bilinear_actionNumerator {form : Form K}
    (value : form.EvenClifford) (left right : Vector3 K) :
    form.bilinear (EvenClifford.actionNumerator value left)
        (EvenClifford.actionNumerator value right) =
      (EvenClifford.norm value) ^ 2 * form.bilinear left right := by
  have leftAxisCross :
      form.bilinear value.vector
          (form.cliffordCross right value.vector) = 0 := by
    rw [form.bilinear_comm]
    exact form.cliffordCross_perpendicular_right right value.vector
  have rightAxisCross :
      form.bilinear (form.cliffordCross left value.vector)
          value.vector = 0 :=
    form.cliffordCross_perpendicular_right left value.vector
  have core :
      form.bilinear
          (Vector3.add
            (Vector3.scale
              (value.scalar ^ 2 -
                form.determinant * form.quadrance value.vector)
              left)
            (Vector3.scale
              (2 * form.determinant *
                form.bilinear left value.vector)
              value.vector))
          (Vector3.add
            (Vector3.scale
              (value.scalar ^ 2 -
                form.determinant * form.quadrance value.vector)
              right)
            (Vector3.scale
              (2 * form.determinant *
                form.bilinear right value.vector)
              value.vector)) =
        (value.scalar ^ 2 -
            form.determinant * form.quadrance value.vector) ^ 2 *
            form.bilinear left right +
          4 * form.determinant * value.scalar ^ 2 *
            form.bilinear left value.vector *
            form.bilinear right value.vector := by
    rw [form.bilinear_add_left, form.bilinear_add_right,
      form.bilinear_add_right,
      form.bilinear_scale_left, form.bilinear_scale_right,
      form.bilinear_scale_left, form.bilinear_scale_right,
      form.bilinear_scale_left, form.bilinear_scale_right,
      form.bilinear_scale_left, form.bilinear_scale_right]
    rw [form.bilinear_comm value.vector right]
    unfold Form.quadrance
    ring1
  have mixed :
      form.bilinear
          (Vector3.add
            (Vector3.scale
              (value.scalar ^ 2 -
                form.determinant * form.quadrance value.vector)
              left)
            (Vector3.scale
              (2 * form.determinant *
                form.bilinear left value.vector)
              value.vector))
          (Vector3.scale (-2 * value.scalar)
            (form.cliffordCross right value.vector)) +
        form.bilinear
          (Vector3.scale (-2 * value.scalar)
            (form.cliffordCross left value.vector))
          (Vector3.add
            (Vector3.scale
              (value.scalar ^ 2 -
                form.determinant * form.quadrance value.vector)
              right)
            (Vector3.scale
              (2 * form.determinant *
                form.bilinear right value.vector)
              value.vector)) = 0 := by
    rw [form.bilinear_add_left, form.bilinear_add_right,
      form.bilinear_scale_left, form.bilinear_scale_right,
      form.bilinear_scale_left, form.bilinear_scale_right,
      form.bilinear_scale_left, form.bilinear_scale_right,
      form.bilinear_scale_left, form.bilinear_scale_right,
      leftAxisCross, rightAxisCross,
      form.bilinear_cliffordCross_swap left right value.vector]
    ring1
  have cross :
      form.bilinear
          (Vector3.scale (-2 * value.scalar)
            (form.cliffordCross left value.vector))
          (Vector3.scale (-2 * value.scalar)
            (form.cliffordCross right value.vector)) =
        4 * value.scalar ^ 2 * form.determinant *
          (form.bilinear left right * form.quadrance value.vector -
            form.bilinear left value.vector *
              form.bilinear right value.vector) := by
    rw [form.bilinear_scale_left, form.bilinear_scale_right,
      form.bilinear_cliffordCross_pair,
      form.bilinear_comm value.vector right]
    unfold Form.quadrance
    ring1
  let leftCore := Vector3.add
    (Vector3.scale
      (value.scalar ^ 2 -
        form.determinant * form.quadrance value.vector) left)
    (Vector3.scale
      (2 * form.determinant * form.bilinear left value.vector)
      value.vector)
  let rightCore := Vector3.add
    (Vector3.scale
      (value.scalar ^ 2 -
        form.determinant * form.quadrance value.vector) right)
    (Vector3.scale
      (2 * form.determinant * form.bilinear right value.vector)
      value.vector)
  let leftCross := Vector3.scale (-2 * value.scalar)
    (form.cliffordCross left value.vector)
  let rightCross := Vector3.scale (-2 * value.scalar)
    (form.cliffordCross right value.vector)
  change form.bilinear leftCore rightCore = _ at core
  change form.bilinear leftCore rightCross +
    form.bilinear leftCross rightCore = 0 at mixed
  change form.bilinear leftCross rightCross = _ at cross
  change form.bilinear (Vector3.add leftCore leftCross)
    (Vector3.add rightCore rightCross) = _
  calc
    form.bilinear (Vector3.add leftCore leftCross)
        (Vector3.add rightCore rightCross) =
      (form.bilinear leftCore rightCore +
        form.bilinear leftCore rightCross) +
      (form.bilinear leftCross rightCore +
        form.bilinear leftCross rightCross) := by
      rw [form.bilinear_add_left,
        form.bilinear_add_right leftCore rightCore rightCross,
        form.bilinear_add_right leftCross rightCore rightCross]
    _ = form.bilinear leftCore rightCore +
        (form.bilinear leftCore rightCross +
          form.bilinear leftCross rightCore) +
        form.bilinear leftCross rightCross := by ring1
    _ = (value.scalar ^ 2 -
          form.determinant * form.quadrance value.vector) ^ 2 *
          form.bilinear left right +
        4 * form.determinant * value.scalar ^ 2 *
          form.bilinear left value.vector *
          form.bilinear right value.vector +
        0 +
        4 * value.scalar ^ 2 * form.determinant *
          (form.bilinear left right * form.quadrance value.vector -
            form.bilinear left value.vector *
              form.bilinear right value.vector) := by
      rw [core, mixed, cross]
    _ = (EvenClifford.norm value) ^ 2 * form.bilinear left right := by
      unfold EvenClifford.norm
      ring1

end EvenClifford
namespace NonNullEvenClifford

/-- Normalize the Clifford action numerator by the inverse of the retained nonzero norm.

The resulting vector operation preserves the indexed bilinear form and its quadrance. -/
def action {form : Form K} (value :
  form.NonNullEvenClifford)
    (vector : Vector3 K) : Vector3 K :=
  Vector3.scale (EvenClifford.norm value.toEvenClifford)⁻¹
    (EvenClifford.actionNumerator value.toEvenClifford vector)

/-- Scale the displayed action-numerator matrix by the inverse of the original nonzero norm. -/
def actionMatrix {form : Form K}
    (value : form.NonNullEvenClifford) : Matrix3 K :=
  Matrix3.scale (EvenClifford.norm value.toEvenClifford)⁻¹
    (EvenClifford.actionNumeratorMatrix value.toEvenClifford)

/-- The normalized Clifford action is orientation preserving. -/
theorem determinant_actionMatrix {form :
  Form K}
    (value : form.NonNullEvenClifford) :
    Matrix3.determinant (NonNullEvenClifford.actionMatrix value) = 1 := by
  have cancel := ExplicitField.mul_inv_cancel
    (EvenClifford.norm value.toEvenClifford) value.normNonzero
  have reverseCancel :
      (EvenClifford.norm value.toEvenClifford)⁻¹ * (EvenClifford.norm value.toEvenClifford) = 1 := by
    calc
      (EvenClifford.norm value.toEvenClifford)⁻¹ * (EvenClifford.norm value.toEvenClifford) =
          (EvenClifford.norm value.toEvenClifford) * (EvenClifford.norm value.toEvenClifford)⁻¹ := by
        ring1
      _ = 1 := cancel
  have cubeCancel :
      (EvenClifford.norm value.toEvenClifford)⁻¹ ^ 3 *
          (EvenClifford.norm value.toEvenClifford) ^ 3 = 1 := by
    calc
      (EvenClifford.norm value.toEvenClifford)⁻¹ ^ 3 *
          (EvenClifford.norm value.toEvenClifford) ^ 3 =
        ((EvenClifford.norm value.toEvenClifford)⁻¹ *
          (EvenClifford.norm value.toEvenClifford)) ^ 3 := by
        ring1
      _ = 1 := by rw [reverseCancel]; ring1
  unfold NonNullEvenClifford.actionMatrix
  rw [Matrix3.determinant_scale,
    EvenClifford.determinant_actionNumeratorMatrix, cubeCancel]

/-- Row multiplication by the normalized action matrix computes the normalized Clifford action. -/
theorem rowMul_actionMatrix {form : Form
  K}
    (value : form.NonNullEvenClifford) (vector : Vector3 K) :
    Matrix3.rowMul vector (NonNullEvenClifford.actionMatrix value) = (NonNullEvenClifford.action value) vector := by
  unfold NonNullEvenClifford.actionMatrix NonNullEvenClifford.action
  rw [Matrix3.rowMul_scale,
    EvenClifford.rowMul_actionNumeratorMatrix]

/-- The normalized non-null Clifford action fixes its own vector coordinate. -/
theorem action_vector {form : Form K} (value : form.NonNullEvenClifford) :
    action value value.toEvenClifford.vector = value.toEvenClifford.vector := by
  have cancel : (EvenClifford.norm value.toEvenClifford)⁻¹ *
      EvenClifford.norm value.toEvenClifford = 1 := by
    rw [mul_comm, ExplicitField.mul_inv_cancel _ value.normNonzero]
  unfold action
  rw [EvenClifford.actionNumerator_vector, Vector3.scale_scale, cancel, Vector3.one_scale]

/-- A non-null scalar Clifford value acts as the identity on every vector. -/
theorem action_of_vector_eq_zero {form : Form K} (value : form.NonNullEvenClifford)
    (vectorZero : value.toEvenClifford.vector = Vector3.zero) (vector : Vector3 K) :
    action value vector = vector := by
  have cancel : (EvenClifford.norm value.toEvenClifford)⁻¹ *
      EvenClifford.norm value.toEvenClifford = 1 := by
    rw [mul_comm, ExplicitField.mul_inv_cancel _ value.normNonzero]
  unfold action
  rw [EvenClifford.actionNumerator_of_vector_eq_zero _ vectorZero,
    Vector3.scale_scale, cancel, Vector3.one_scale]

/-- Construct a nonzero fixed vector for a non-null Clifford action.

The vector coordinate is selected when it is nonzero. For a scalar value,
the action is the identity and the supplied nonzero fallback vector is retained.
Both branches certify row action by the original normalized matrix.
-/
def fixedVector [DecidableEq K] {form : Form K} (value : form.NonNullEvenClifford)
    (fallback : Vector3 K) (fallbackNonzero : fallback ≠ Vector3.zero) :
    Σ' vector : Vector3 K, vector ≠ Vector3.zero ∧ Matrix3.rowMul vector (actionMatrix value) = vector :=
  if vectorZero : value.toEvenClifford.vector = Vector3.zero then
    ⟨fallback, fallbackNonzero, by
      rw [rowMul_actionMatrix]
      exact action_of_vector_eq_zero value vectorZero fallback⟩
  else
    ⟨value.toEvenClifford.vector, vectorZero, by
      rw [rowMul_actionMatrix]
      exact action_vector value⟩

/-- The normalized non-null Clifford action preserves the indexed vector quadrance. -/
theorem quadrance_action {form : Form K}
    (value : form.NonNullEvenClifford) (vector : Vector3 K) :
    form.quadrance ((NonNullEvenClifford.action value) vector) = form.quadrance vector := by
  have cancel := ExplicitField.mul_inv_cancel
    (EvenClifford.norm value.toEvenClifford) value.normNonzero
  have reverseCancel :
      (EvenClifford.norm value.toEvenClifford)⁻¹ * (EvenClifford.norm value.toEvenClifford) = 1 := by
    calc
      (EvenClifford.norm value.toEvenClifford)⁻¹ * (EvenClifford.norm value.toEvenClifford) =
          (EvenClifford.norm value.toEvenClifford) * (EvenClifford.norm value.toEvenClifford)⁻¹ := by
        ring1
      _ = 1 := cancel
  unfold NonNullEvenClifford.action
  rw [form.quadrance_scale, EvenClifford.quadrance_actionNumerator]
  calc
    (EvenClifford.norm value.toEvenClifford)⁻¹ ^ 2 *
        ((EvenClifford.norm value.toEvenClifford) ^ 2 * form.quadrance vector) =
      ((EvenClifford.norm value.toEvenClifford)⁻¹ *
        (EvenClifford.norm value.toEvenClifford)) ^ 2 * form.quadrance vector := by
      ring1
    _ = form.quadrance vector := by rw [reverseCancel]; ring1

/-- The normalized non-null Clifford action preserves the complete indexed bilinear pairing. -/
theorem bilinear_action {form : Form K}
    (value : form.NonNullEvenClifford) (left right : Vector3 K) :
    form.bilinear ((NonNullEvenClifford.action value) left) ((NonNullEvenClifford.action value) right) =
      form.bilinear left right := by
  have cancel := ExplicitField.mul_inv_cancel
    (EvenClifford.norm value.toEvenClifford) value.normNonzero
  have reverseCancel :
      (EvenClifford.norm value.toEvenClifford)⁻¹ * (EvenClifford.norm value.toEvenClifford) = 1 := by
    calc
      (EvenClifford.norm value.toEvenClifford)⁻¹ * (EvenClifford.norm value.toEvenClifford) =
          (EvenClifford.norm value.toEvenClifford) * (EvenClifford.norm value.toEvenClifford)⁻¹ := by
        ring1
      _ = 1 := cancel
  unfold NonNullEvenClifford.action
  rw [form.bilinear_scale_left, form.bilinear_scale_right,
    EvenClifford.bilinear_actionNumerator]
  calc
    (EvenClifford.norm value.toEvenClifford)⁻¹ *
        ((EvenClifford.norm value.toEvenClifford)⁻¹ *
          ((EvenClifford.norm value.toEvenClifford) ^ 2 * form.bilinear left right)) =
      ((EvenClifford.norm value.toEvenClifford)⁻¹ *
        (EvenClifford.norm value.toEvenClifford)) ^ 2 * form.bilinear left right := by
      ring1
    _ = form.bilinear left right := by rw [reverseCancel]; ring1

/-- The normalized action matrix preserves the retained form matrix.

For the row-vector convention, the matrix multiplied by the form and then its own transpose equals the original form. -/
theorem actionMatrix_preservesMatrix {form
  : Form K}
    (value : form.NonNullEvenClifford) :
    Matrix3.mul (Matrix3.mul (NonNullEvenClifford.actionMatrix value) form.matrix)
      (Matrix3.transpose (NonNullEvenClifford.actionMatrix value)) = form.matrix := by
  apply form.preservesMatrix_of_bilinear_rowMul
  intro left right
  rw [(NonNullEvenClifford.rowMul_actionMatrix value), (NonNullEvenClifford.rowMul_actionMatrix value)]
  exact (NonNullEvenClifford.bilinear_action value) left right

/-- Cached inverse matrix obtained from the form matrix, the transpose action,
and the cached inverse form matrix. -/
def actionInverseMatrix {form : Form K}
    (value : form.NonNullEvenClifford) : Matrix3 K :=
  Matrix3.mul
    (Matrix3.mul form.matrix (Matrix3.transpose (NonNullEvenClifford.actionMatrix value)))
    form.inverse

/-- The cached action inverse is a right inverse of the normalized action matrix. -/
theorem
  actionMatrix_mul_actionInverseMatrix
  {form : Form K}
    (value : form.NonNullEvenClifford) :
    Matrix3.mul (NonNullEvenClifford.actionMatrix value) (NonNullEvenClifford.actionInverseMatrix value) =
      Matrix3.identity := by
  unfold NonNullEvenClifford.actionInverseMatrix
  calc
    Matrix3.mul (NonNullEvenClifford.actionMatrix value)
        (Matrix3.mul
          (Matrix3.mul form.matrix
            (Matrix3.transpose (NonNullEvenClifford.actionMatrix value)))
          form.inverse) =
      Matrix3.mul (NonNullEvenClifford.actionMatrix value)
        (Matrix3.mul form.matrix
          (Matrix3.mul (Matrix3.transpose (NonNullEvenClifford.actionMatrix value))
            form.inverse)) := by
      rw [Matrix3.mul_assoc]
    _ = Matrix3.mul
        (Matrix3.mul (NonNullEvenClifford.actionMatrix value) form.matrix)
        (Matrix3.mul (Matrix3.transpose (NonNullEvenClifford.actionMatrix value))
          form.inverse) := by
      rw [Matrix3.mul_assoc]
    _ =
      Matrix3.mul
        (Matrix3.mul
          (Matrix3.mul (NonNullEvenClifford.actionMatrix value) form.matrix)
          (Matrix3.transpose (NonNullEvenClifford.actionMatrix value)))
        form.inverse := by
      exact (Matrix3.mul_assoc
        (Matrix3.mul (NonNullEvenClifford.actionMatrix value) form.matrix)
        (Matrix3.transpose (NonNullEvenClifford.actionMatrix value)) form.inverse).symm
    _ = Matrix3.mul form.matrix form.inverse := by
      rw [(NonNullEvenClifford.actionMatrix_preservesMatrix value)]
    _ = Matrix3.identity := form.matrix_mul_inverse

/-- The cached action inverse is a left inverse of the normalized action matrix. -/
theorem
  actionInverseMatrix_mul_actionMatrix
  {form : Form K}
    (value : form.NonNullEvenClifford) :
    Matrix3.mul (NonNullEvenClifford.actionInverseMatrix value) (NonNullEvenClifford.actionMatrix value) =
      Matrix3.identity :=
  Matrix3.inverse_mul_of_mul_eq_identity form.one_ne_zero
    (NonNullEvenClifford.actionMatrix_mul_actionInverseMatrix value)
end NonNullEvenClifford

end Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm
