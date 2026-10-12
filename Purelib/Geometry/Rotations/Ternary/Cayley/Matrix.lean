module

public import Purelib.Geometry.Rotations.Ternary.Cayley
public import Purelib.Geometry.Rotations.Ternary.Characteristic
import Purelib.Algebra.Clifford.Ternary.Action
import Purelib.Algebra.Clifford.Ternary.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring

/-!
# Matrix formulas for form-relative Cayley caps

The original scalar-one Clifford cap is a quadratic polynomial in its skew
matrix. Its denominator also certifies both resolvent determinants, so the
finite matrix formulas retain the original form and cap owners.
-/

public section

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm
open Purelib.Geometry.Rotations.Ternary
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K] (form : TernaryForm K)

/-- The form-relative skew cube is negative determinant-weighted quadrance times the skew matrix. -/
theorem actionSkew_cube (axis : Vector3 K) :
    Matrix3.mul (Matrix3.mul (form.actionSkew axis) (form.actionSkew axis))
        (form.actionSkew axis) =
      Matrix3.scale (-(form.determinant * form.quadrance axis)) (form.actionSkew axis) := by
  apply Matrix3.eq_of_rowMul_eq
  intro vector
  rw [← Matrix3.rowMul_mul, form.rowMul_actionSkew, form.actionSkew_square,
    Matrix3.rowMul_sub, Matrix3.rowMul_scale, Matrix3.rowMul_outer,
    Matrix3.rowMul_scale, Matrix3.rowMul_identity,
    form.cliffordCross_sub_right, form.cliffordCross_scale_right,
    form.cliffordCross_scale_right, form.cliffordCross_scale_right,
    form.cliffordCross_self, Matrix3.rowMul_scale, form.rowMul_actionSkew]
  ext <;> unfold Vector3.sub Vector3.scale Vector3.zero <;> ring1

/-- The determinant of identity minus a relative skew matrix is the original cap denominator. -/
theorem determinant_identity_sub_actionSkew (axis : Vector3 K) :
    Matrix3.determinant (Matrix3.sub Matrix3.identity (form.actionSkew axis)) =
      Cayley.TernaryForm.cayleyDenominator form axis := by
  have polynomial := Matrix3.determinant_quadratic_polynomial (form.actionSkew axis) 1 (-1) 0
  rw [form.trace_actionSkew, form.principalTrace_actionSkew, form.determinant_actionSkew] at polynomial
  calc
    Matrix3.determinant (Matrix3.sub Matrix3.identity (form.actionSkew axis)) =
        Matrix3.determinant (Matrix3.add
          (Matrix3.add (Matrix3.scale 1 Matrix3.identity) (Matrix3.scale (-1) (form.actionSkew axis)))
          (Matrix3.scale 0 (Matrix3.mul (form.actionSkew axis) (form.actionSkew axis)))) := by
      congr 1
      ext <;> unfold Matrix3.sub Matrix3.add Matrix3.scale <;> ring1
    _ = Cayley.TernaryForm.cayleyDenominator form axis := by
      rw [polynomial]
      unfold Cayley.TernaryForm.cayleyDenominator
      ring1

/-- The determinant of identity plus a relative skew matrix has the same cap denominator. -/
theorem determinant_identity_add_actionSkew (axis : Vector3 K) :
    Matrix3.determinant (Matrix3.add Matrix3.identity (form.actionSkew axis)) =
      Cayley.TernaryForm.cayleyDenominator form axis := by
  have polynomial := Matrix3.determinant_quadratic_polynomial (form.actionSkew axis) 1 1 0
  rw [form.trace_actionSkew, form.principalTrace_actionSkew, form.determinant_actionSkew] at polynomial
  calc
    Matrix3.determinant (Matrix3.add Matrix3.identity (form.actionSkew axis)) =
        Matrix3.determinant (Matrix3.add
          (Matrix3.add (Matrix3.scale 1 Matrix3.identity) (Matrix3.scale 1 (form.actionSkew axis)))
          (Matrix3.scale 0 (Matrix3.mul (form.actionSkew axis) (form.actionSkew axis)))) := by
      congr 1
      ext <;> unfold Matrix3.add Matrix3.scale <;> ring1
    _ = Cayley.TernaryForm.cayleyDenominator form axis := by
      rw [polynomial]
      unfold Cayley.TernaryForm.cayleyDenominator
      ring1

/-- The original Clifford cap matrix is the quadratic Cayley formula.

The retained nonzero denominator cancels its original inverse. No second cap
algorithm or fresh matrix inversion is introduced.
-/
theorem capRotation_matrix_quadratic (axis : Vector3 K)
    (defined : Cayley.TernaryForm.cayleyDenominator form axis ≠ 0) :
    (Cayley.TernaryForm.capRotation form axis defined).matrix =
      Matrix3.add Matrix3.identity
        (Matrix3.scale (2 / Cayley.TernaryForm.cayleyDenominator form axis)
          (Matrix3.add (form.actionSkew axis)
            (Matrix3.mul (form.actionSkew axis) (form.actionSkew axis)))) := by
  change Matrix3.scale _ (EvenClifford.actionNumeratorMatrix _) = _
  rw [EvenClifford.actionNumeratorMatrix_eq_quadratic]
  have normEqual : EvenClifford.norm (Cayley.TernaryForm.capValue form axis defined).toEvenClifford =
      Cayley.TernaryForm.cayleyDenominator form axis :=
    Cayley.TernaryForm.norm_capRepresentative form axis
  rw [normEqual]
  change Matrix3.scale (Cayley.TernaryForm.cayleyDenominator form axis)⁻¹
    (Matrix3.add
      (Matrix3.add (Matrix3.scale (Cayley.TernaryForm.cayleyDenominator form axis) Matrix3.identity)
        (Matrix3.scale (2 * 1) (form.actionSkew axis)))
      (Matrix3.scale 2 (Matrix3.mul (form.actionSkew axis) (form.actionSkew axis)))) = _
  have cancel := ExplicitField.mul_inv_cancel (Cayley.TernaryForm.cayleyDenominator form axis) defined
  have normalized : Matrix3.scale (Cayley.TernaryForm.cayleyDenominator form axis)⁻¹
      (Matrix3.scale (Cayley.TernaryForm.cayleyDenominator form axis) Matrix3.identity) =
      Matrix3.identity := by
    rw [Matrix3.scale_scale, mul_comm, cancel, Matrix3.one_scale]
  calc
    _ = Matrix3.add
        (Matrix3.scale (Cayley.TernaryForm.cayleyDenominator form axis)⁻¹
          (Matrix3.scale (Cayley.TernaryForm.cayleyDenominator form axis) Matrix3.identity))
        (Matrix3.scale (2 / Cayley.TernaryForm.cayleyDenominator form axis)
          (Matrix3.add (form.actionSkew axis)
            (Matrix3.mul (form.actionSkew axis) (form.actionSkew axis)))) := by
      ext <;> unfold Matrix3.scale Matrix3.add <;>
        rw [ExplicitField.div_eq_mul_inv] <;> ring1
    _ = _ := by rw [normalized]

/-- The explicit inverse of identity minus a relative skew matrix.

The original cap denominator certifies invertibility of the displayed
resolvent. The inverse uses the owned finite adjugate operation.
-/
@[expose] def actionSkewResolventInverse (axis : Vector3 K)
    (defined : Cayley.TernaryForm.cayleyDenominator form axis ≠ 0) : Matrix3 K :=
  Matrix3.inverse (Matrix3.sub Matrix3.identity (form.actionSkew axis))
    (by rw [form.determinant_identity_sub_actionSkew]; exact defined)

/-- The resolvent inverse is a quadratic polynomial in the original skew matrix.

The cubic relation and retained nonzero denominator certify the displayed
candidate as a right inverse; the owned inverse certificate identifies it
with the actual resolvent inverse.
-/
theorem actionSkewResolventInverse_eq (axis : Vector3 K)
    (defined : Cayley.TernaryForm.cayleyDenominator form axis ≠ 0) :
    form.actionSkewResolventInverse axis defined =
      Matrix3.add Matrix3.identity
        (Matrix3.scale (1 / Cayley.TernaryForm.cayleyDenominator form axis)
          (Matrix3.add (form.actionSkew axis)
            (Matrix3.mul (form.actionSkew axis) (form.actionSkew axis)))) := by
  let denominator := Cayley.TernaryForm.cayleyDenominator form axis
  let skew := form.actionSkew axis
  let candidate := Matrix3.add Matrix3.identity
    (Matrix3.scale (1 / denominator) (Matrix3.add skew (Matrix3.mul skew skew)))
  have rightInverse : Matrix3.mul (Matrix3.sub Matrix3.identity skew) candidate =
      Matrix3.identity := by
    have cancel := ExplicitField.mul_inv_cancel denominator defined
    calc
      _ = Matrix3.sub
          (Matrix3.add Matrix3.identity (Matrix3.scale (denominator⁻¹ - 1) skew))
          (Matrix3.scale denominator⁻¹ (Matrix3.mul (Matrix3.mul skew skew) skew)) := by
        dsimp only [candidate]
        rw [ExplicitField.div_eq_mul_inv, one_mul]
        exact Matrix3.resolvent_mul_quadratic skew denominator⁻¹
      _ = Matrix3.add Matrix3.identity (Matrix3.scale (denominator * denominator⁻¹ - 1) skew) := by
        rw [form.actionSkew_cube]
        ext <;> unfold Matrix3.sub Matrix3.add Matrix3.scale denominator
          Cayley.TernaryForm.cayleyDenominator <;> ring1
      _ = Matrix3.identity := by
        rw [cancel]
        ext <;> unfold Matrix3.add Matrix3.scale <;> ring1
  unfold actionSkewResolventInverse
  change Matrix3.inverse (Matrix3.sub Matrix3.identity skew) _ = candidate
  calc
    _ = Matrix3.mul (Matrix3.inverse (Matrix3.sub Matrix3.identity skew) _)
        Matrix3.identity := by rw [Matrix3.mul_identity]
    _ = Matrix3.mul (Matrix3.inverse (Matrix3.sub Matrix3.identity skew) _)
        (Matrix3.mul (Matrix3.sub Matrix3.identity skew) candidate) := by rw [rightInverse]
    _ = Matrix3.mul
        (Matrix3.mul (Matrix3.inverse (Matrix3.sub Matrix3.identity skew) _)
          (Matrix3.sub Matrix3.identity skew)) candidate := by rw [Matrix3.mul_assoc]
    _ = candidate := by rw [Matrix3.inverse_mul, Matrix3.identity_mul]

/-- Multiplying a cap by its skew resolvent gives identity plus the skew matrix. -/
theorem capRotation_matrix_mul_resolvent (axis : Vector3 K)
    (defined : Cayley.TernaryForm.cayleyDenominator form axis ≠ 0) :
    Matrix3.mul (Cayley.TernaryForm.capRotation form axis defined).matrix
        (Matrix3.sub Matrix3.identity (form.actionSkew axis)) =
      Matrix3.add Matrix3.identity (form.actionSkew axis) := by
  rw [form.capRotation_matrix_quadratic]
  let denominator := Cayley.TernaryForm.cayleyDenominator form axis
  let skew := form.actionSkew axis
  have cancel := ExplicitField.mul_inv_cancel denominator defined
  calc
    _ = Matrix3.sub
        (Matrix3.add Matrix3.identity (Matrix3.scale (2 * denominator⁻¹ - 1) skew))
        (Matrix3.scale (2 * denominator⁻¹) (Matrix3.mul (Matrix3.mul skew skew) skew)) := by
      rw [ExplicitField.div_eq_mul_inv]
      exact Matrix3.quadratic_mul_resolvent skew (2 * denominator⁻¹)
    _ = Matrix3.add Matrix3.identity (Matrix3.scale (2 * (denominator * denominator⁻¹) - 1) skew) := by
      rw [form.actionSkew_cube]
      ext <;> unfold Matrix3.sub Matrix3.add Matrix3.scale denominator
        Cayley.TernaryForm.cayleyDenominator <;> ring1
    _ = Matrix3.add Matrix3.identity skew := by
      rw [cancel]
      ext <;> unfold Matrix3.add Matrix3.scale <;> ring1

/-- The original Clifford cap is the Cayley product with the actual resolvent inverse. -/
theorem capRotation_matrix_eq_cayley (axis : Vector3 K)
    (defined : Cayley.TernaryForm.cayleyDenominator form axis ≠ 0) :
    (Cayley.TernaryForm.capRotation form axis defined).matrix =
      Matrix3.mul (Matrix3.add Matrix3.identity (form.actionSkew axis))
        (form.actionSkewResolventInverse axis defined) := by
  have product := form.capRotation_matrix_mul_resolvent axis defined
  calc
    _ = Matrix3.mul (Cayley.TernaryForm.capRotation form axis defined).matrix
        (Matrix3.mul (Matrix3.sub Matrix3.identity (form.actionSkew axis))
          (form.actionSkewResolventInverse axis defined)) := by
      unfold actionSkewResolventInverse
      rw [Matrix3.mul_inverse, Matrix3.mul_identity]
    _ = Matrix3.mul
        (Matrix3.mul (Cayley.TernaryForm.capRotation form axis defined).matrix
          (Matrix3.sub Matrix3.identity (form.actionSkew axis)))
        (form.actionSkewResolventInverse axis defined) := by rw [Matrix3.mul_assoc]
    _ = _ := by rw [product]

/-- Minus one cannot have a nonzero eigenvector in a defined ternary cap.

Transporting the purported eigenvector through the skew resolvent cancels
its skew terms, leaving twice the original vector equal to zero.
-/
theorem rowMul_capRotation_eq_neg_implies_zero (axis : Vector3 K)
    (defined : Cayley.TernaryForm.cayleyDenominator form axis ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) (vector : Vector3 K)
    (negativeEigen : Matrix3.rowMul vector (Cayley.TernaryForm.capRotation form axis defined).matrix =
      Vector3.neg vector) : vector = Vector3.zero := by
  have transported := congrArg
    (fun result => Matrix3.rowMul result (Matrix3.sub Matrix3.identity (form.actionSkew axis))) negativeEigen
  rw [Matrix3.rowMul_mul, form.capRotation_matrix_mul_resolvent] at transported
  have difference :
      Vector3.sub (Matrix3.rowMul vector (Matrix3.add Matrix3.identity (form.actionSkew axis)))
        (Matrix3.rowMul (Vector3.neg vector) (Matrix3.sub Matrix3.identity (form.actionSkew axis))) =
      Vector3.scale 2 vector := by
    ext <;> unfold Vector3.sub Matrix3.rowMul Matrix3.add Matrix3.sub Matrix3.identity
      Vector3.neg Vector3.scale <;> ring1
  have twiceZero : Vector3.scale 2 vector = Vector3.zero := by
    calc
      _ = Vector3.sub
          (Matrix3.rowMul vector (Matrix3.add Matrix3.identity (form.actionSkew axis)))
          (Matrix3.rowMul (Vector3.neg vector) (Matrix3.sub Matrix3.identity (form.actionSkew axis))) := difference.symm
      _ = Vector3.zero := by
        rw [transported]
        ext <;> unfold Vector3.sub Vector3.zero <;> ring1
  apply Vector3.ext
  · exact ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero (congrArg Vector3.t twiceZero)
  · exact ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero (congrArg Vector3.r twiceZero)
  · exact ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero (congrArg Vector3.s twiceZero)

/-- The fixed vectors of a form-relative cap are exactly the kernel of its original skew matrix.

The retained resolvent relation identifies both kernels when two is nonzero,
without selecting a basis or eigenvector. -/
theorem rowMul_capRotation_eq_self_iff_skew_kernel (axis vector : Vector3 K)
    (defined : Cayley.TernaryForm.cayleyDenominator form axis ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.rowMul vector (Cayley.TernaryForm.capRotation form axis defined).matrix = vector ↔
      Matrix3.rowMul vector (form.actionSkew axis) = Vector3.zero := by
  constructor
  · intro fixed
    have transported := congrArg
      (fun value => Matrix3.rowMul value (Matrix3.sub Matrix3.identity (form.actionSkew axis))) fixed
    rw [Matrix3.rowMul_mul, form.capRotation_matrix_mul_resolvent,
      Matrix3.rowMul_add, Matrix3.rowMul_sub, Matrix3.rowMul_identity] at transported
    let kernelValue := Matrix3.rowMul vector (form.actionSkew axis)
    have shifted := congrArg (fun value => Vector3.sub value vector) transported
    have negative : kernelValue = Vector3.neg kernelValue := by
      calc
        kernelValue = Vector3.sub (Vector3.add vector kernelValue) vector := by
          ext <;> unfold Vector3.sub Vector3.add <;> ring1
        _ = Vector3.sub (Vector3.sub vector kernelValue) vector := shifted
        _ = Vector3.neg kernelValue := by
          ext <;> unfold Vector3.sub Vector3.neg <;> ring1
    exact Vector3.eq_zero_of_eq_neg kernelValue twoNonzero negative
  · intro kernel
    have zeroAction : Matrix3.rowMul Vector3.zero (form.actionSkew axis) = Vector3.zero := by
      ext <;> unfold Matrix3.rowMul Vector3.zero <;> ring1
    rw [form.capRotation_matrix_quadratic, Matrix3.rowMul_add, Matrix3.rowMul_identity,
      Matrix3.rowMul_scale, Matrix3.rowMul_add, ← Matrix3.rowMul_mul, kernel, zeroAction,
      Vector3.zero_add, Vector3.scale_zero, Vector3.add_zero]

/-- The characteristic polynomial of any ternary rotation is determined by its trace half spread. -/
theorem characteristicValue_rotation_halfSpread (rotation : form.SpecialOrthogonal)
    (twoNonzero : (2 : K) ≠ 0) (X : K) :
    Matrix3.characteristicValue rotation.matrix X =
      (X - 1) * (X ^ 2 -
        2 * (1 - 2 * Cayley.TernaryForm.rotationHalfSpread form rotation) * X + 1) := by
  have fourNonzero := Purelib.Algebra.Field.Characteristic.Nonzero.four_ne_zero twoNonzero
  have fourCancellation : 4 * Cayley.TernaryForm.rotationHalfSpread form rotation =
      3 - Matrix3.trace rotation.matrix := by
    unfold Cayley.TernaryForm.rotationHalfSpread
    rw [mul_comm]
    exact ExplicitField.div_mul_cancel _ fourNonzero
  have coefficient : Matrix3.trace rotation.matrix - 1 =
      2 * (1 - 2 * Cayley.TernaryForm.rotationHalfSpread form rotation) := by
    calc
      _ = 2 * (1 - 2 * Cayley.TernaryForm.rotationHalfSpread form rotation) +
          (4 * Cayley.TernaryForm.rotationHalfSpread form rotation -
            (3 - Matrix3.trace rotation.matrix)) := by ring1
      _ = _ := by rw [fourCancellation]; ring1
  rw [rotation.characteristicValue_matrix, coefficient]

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm
