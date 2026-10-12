module

public import Purelib.Geometry.Rotations.Ternary.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Tactic.Ring

/-!
# Characteristic polynomials of displayed ternary rotations

The retained two-sided inverse and Gram-matrix preservation identify the
adjugate and its trace. Every form-indexed rotation therefore has the same
reciprocal quadratic factor after its fixed-direction factor.
-/

public section

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm.SpecialOrthogonal

open Purelib.Algebra.Field (ExplicitField)
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)

variable {K : Type*} [ExplicitField K] {form : TernaryForm K}

/-- The adjugate of a determinant-one ternary rotation is its retained inverse matrix. -/
theorem adjugate_matrix (rotation : form.SpecialOrthogonal) :
    Matrix3.adjugate rotation.matrix = rotation.inverseMatrix := by
  have adjugateProduct : Matrix3.mul (Matrix3.adjugate rotation.matrix) rotation.matrix =
      Matrix3.identity := by
    rw [Matrix3.adjugate_mul, rotation.determinantOne, Matrix3.one_scale]
  calc
    _ = Matrix3.mul (Matrix3.adjugate rotation.matrix) Matrix3.identity := by rw [Matrix3.mul_identity]
    _ = Matrix3.mul (Matrix3.adjugate rotation.matrix)
        (Matrix3.mul rotation.matrix rotation.inverseMatrix) := by rw [rotation.matrix_mul_inverse]
    _ = Matrix3.mul (Matrix3.mul (Matrix3.adjugate rotation.matrix) rotation.matrix)
        rotation.inverseMatrix := by rw [Matrix3.mul_assoc]
    _ = rotation.inverseMatrix := by rw [adjugateProduct, Matrix3.identity_mul]

/-- The retained rotation inverse is the Gram conjugate of the transpose.

The formula uses the original form matrix and its original cached inverse.
It follows from their two-sided inverse certificates and matrix preservation.
-/
theorem inverseMatrix_eq_transpose_conjugate (rotation : form.SpecialOrthogonal) :
    rotation.inverseMatrix =
      Matrix3.mul (Matrix3.mul form.matrix (Matrix3.transpose rotation.matrix)) form.inverse := by
  have gramTranspose : Matrix3.mul form.matrix (Matrix3.transpose rotation.matrix) =
      Matrix3.mul rotation.inverseMatrix form.matrix := by
    calc
      _ = Matrix3.mul (Matrix3.mul rotation.inverseMatrix rotation.matrix)
          (Matrix3.mul form.matrix (Matrix3.transpose rotation.matrix)) := by
        rw [rotation.inverse_mul_matrix, Matrix3.identity_mul]
      _ = Matrix3.mul rotation.inverseMatrix
          (Matrix3.mul (Matrix3.mul rotation.matrix form.matrix) (Matrix3.transpose rotation.matrix)) := by
        rw [Matrix3.mul_assoc, Matrix3.mul_assoc]
      _ = Matrix3.mul rotation.inverseMatrix form.matrix := by rw [rotation.preservesMatrix]
  rw [gramTranspose, Matrix3.mul_assoc, form.matrix_mul_inverse, Matrix3.mul_identity]

/-- The retained inverse of a ternary rotation has the same trace as its original matrix. -/
theorem trace_inverseMatrix (rotation : form.SpecialOrthogonal) :
    Matrix3.trace rotation.inverseMatrix = Matrix3.trace rotation.matrix := by
  rw [inverseMatrix_eq_transpose_conjugate, Matrix3.trace_mul_comm,
    ← Matrix3.mul_assoc, form.inverse_mul_matrix, Matrix3.identity_mul, Matrix3.trace_transpose]

/-- A ternary rotation has equal trace and principal trace for its original displayed matrix. -/
theorem principalTrace_matrix (rotation : form.SpecialOrthogonal) :
    Matrix3.principalTrace rotation.matrix = Matrix3.trace rotation.matrix := by
  unfold Matrix3.principalTrace
  rw [adjugate_matrix, inverseMatrix_eq_transpose_conjugate, Matrix3.trace_mul_comm,
    ← Matrix3.mul_assoc, form.inverse_mul_matrix, Matrix3.identity_mul, Matrix3.trace_transpose]

/-- The characteristic polynomial of a ternary rotation has a fixed-direction factor.

The reciprocal quadratic factor has coefficient trace minus one and constant
one. The equality is pointwise in the supplied field and uses no choice of
eigenvectors or roots.
-/
theorem characteristicValue_matrix (rotation : form.SpecialOrthogonal) (X : K) :
    Matrix3.characteristicValue rotation.matrix X =
      (X - 1) * (X ^ 2 - (Matrix3.trace rotation.matrix - 1) * X + 1) := by
  rw [Matrix3.characteristicValue_expansion, principalTrace_matrix, rotation.determinantOne]
  ring1

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm.SpecialOrthogonal
