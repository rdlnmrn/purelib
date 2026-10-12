module

import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Coordinates3.Matrix
public import Purelib.Algebra.Quadratic.Ternary.Basic
import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Algebra.Quadratic

open Purelib.Algebra.Quadratic.Ternary.Basic

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3

section
@[expose] public section

/-!
# Constructive displayed ternary forms

This module begins the finite coordinate-algebra part of Problem 71.  A form
stores its displayed symmetric matrix together with cached determinant,
adjugate, and inverse data.  The certificates connect every cached value to
the canonical fixed-size matrix calculation, so downstream executable code
does not repeat those calculations or recover an inverse by choice.
-/

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section TernaryForm

/-- A displayed linear action preserving the bilinear form on every pair has the corresponding finite matrix
preservation certificate. -/
theorem preservesMatrix_of_bilinear_rowMul (form :
  Ternary.Basic.TernaryForm K)
    (matrix : Coordinates3.Matrix3 K)
    (preserves : ∀ left right : Coordinates3.Vector K,
      form.bilinear (Matrix3.rowMul left matrix)
          (Matrix3.rowMul right matrix) = form.bilinear left right) :
    Matrix3.mul (Matrix3.mul matrix form.matrix)
      (Matrix3.transpose matrix) = form.matrix := by
  apply Matrix3.ext
  · simpa [TernaryForm.bilinear, Matrix3.rowMul, Matrix3.mul, Matrix3.transpose,
      Coordinates3.Vector.dot] using
      preserves (⟨1, 0, 0⟩ : Coordinates3.Vector K) (⟨1, 0, 0⟩ : Coordinates3.Vector K)
  · simpa [TernaryForm.bilinear, Matrix3.rowMul, Matrix3.mul, Matrix3.transpose,
      Coordinates3.Vector.dot] using
      preserves (⟨1, 0, 0⟩ : Coordinates3.Vector K) (⟨0, 1, 0⟩ : Coordinates3.Vector K)
  · simpa [TernaryForm.bilinear, Matrix3.rowMul, Matrix3.mul, Matrix3.transpose,
      Coordinates3.Vector.dot] using
      preserves (⟨1, 0, 0⟩ : Coordinates3.Vector K) (⟨0, 0, 1⟩ : Coordinates3.Vector K)
  · simpa [TernaryForm.bilinear, Matrix3.rowMul, Matrix3.mul, Matrix3.transpose,
      Coordinates3.Vector.dot] using
      preserves (⟨0, 1, 0⟩ : Coordinates3.Vector K) (⟨1, 0, 0⟩ : Coordinates3.Vector K)
  · simpa [TernaryForm.bilinear, Matrix3.rowMul, Matrix3.mul, Matrix3.transpose,
      Coordinates3.Vector.dot] using
      preserves (⟨0, 1, 0⟩ : Coordinates3.Vector K) (⟨0, 1, 0⟩ : Coordinates3.Vector K)
  · simpa [TernaryForm.bilinear, Matrix3.rowMul, Matrix3.mul, Matrix3.transpose,
      Coordinates3.Vector.dot] using
      preserves (⟨0, 1, 0⟩ : Coordinates3.Vector K) (⟨0, 0, 1⟩ : Coordinates3.Vector K)
  · simpa [TernaryForm.bilinear, Matrix3.rowMul, Matrix3.mul, Matrix3.transpose,
      Coordinates3.Vector.dot] using
      preserves (⟨0, 0, 1⟩ : Coordinates3.Vector K) (⟨1, 0, 0⟩ : Coordinates3.Vector K)
  · simpa [TernaryForm.bilinear, Matrix3.rowMul, Matrix3.mul, Matrix3.transpose,
      Coordinates3.Vector.dot] using
      preserves (⟨0, 0, 1⟩ : Coordinates3.Vector K) (⟨0, 1, 0⟩ : Coordinates3.Vector K)
  · simpa [TernaryForm.bilinear, Matrix3.rowMul, Matrix3.mul, Matrix3.transpose,
      Coordinates3.Vector.dot] using
      preserves (⟨0, 0, 1⟩ : Coordinates3.Vector K) (⟨0, 0, 1⟩ : Coordinates3.Vector K)

/-! ## Form-relative isometries and special orthogonal matrices -/

set_option genInjectivity false in
/-- An executable isometry of a displayed ternary form. Its inverse is cached together with both multiplication
certificates. -/
structure Isometry (form : Ternary.Basic.TernaryForm K) where
  /-- The forward row-action matrix. -/ matrix : Coordinates3.Matrix3 K
  /-- The retained inverse matrix. -/ inverseMatrix : Coordinates3.Matrix3 K
  /-- The forward matrix times the cached inverse is the identity. -/ matrix_mul_inverse : Matrix3.mul matrix
    inverseMatrix = Matrix3.identity
  /-- The cached inverse times the forward matrix is the identity. -/ inverse_mul_matrix : Matrix3.mul inverseMatrix
    matrix = Matrix3.identity
  /-- The forward matrix preserves the displayed bilinear-form matrix. -/ preservesMatrix :
    Matrix3.mul (Matrix3.mul matrix form.matrix)
      (Matrix3.transpose matrix) = form.matrix

constructive_injectivity Isometry

namespace Isometry.mk

end Isometry.mk

namespace Isometry

/-- Right action of a form isometry on a displayed row vector. -/
def act {form : Ternary.Basic.TernaryForm K}
  (isometry : form.Isometry)
    (vector : Coordinates3.Vector K) : Coordinates3.Vector K :=
  Matrix3.rowMul vector isometry.matrix

/-- Cached inverse data are unique, so displayed isometries are equal when their forward matrices are equal. -/
theorem eq_of_matrix_eq {form :
  Ternary.Basic.TernaryForm K}
    (left right : form.Isometry) (matrixEq : left.matrix = right.matrix) :
    left = right := by
  have inverseEq : left.inverseMatrix = right.inverseMatrix := by
    calc
      left.inverseMatrix =
          Matrix3.mul left.inverseMatrix Matrix3.identity :=
        (Matrix3.mul_identity left.inverseMatrix).symm
      _ = Matrix3.mul left.inverseMatrix
          (Matrix3.mul right.matrix right.inverseMatrix) := by
        rw [right.matrix_mul_inverse]
      _ = Matrix3.mul
          (Matrix3.mul left.inverseMatrix right.matrix)
          right.inverseMatrix := by
        rw [Matrix3.mul_assoc]
      _ = Matrix3.mul
          (Matrix3.mul left.inverseMatrix left.matrix)
          right.inverseMatrix := by
        rw [matrixEq]
      _ = Matrix3.mul Matrix3.identity right.inverseMatrix := by
        rw [left.inverse_mul_matrix]
      _ = right.inverseMatrix := Matrix3.identity_mul right.inverseMatrix
  cases left with
  | mk leftMatrix leftInverse leftRight rightLeft leftPreserves =>
      cases right with
      | mk rightMatrix rightInverse rightRight rightLeft' rightPreserves =>
          cases matrixEq
          cases inverseEq
          rfl

/-- The isometry preserves the form on every pair of row vectors. -/
theorem bilinear_act {form :
  Ternary.Basic.TernaryForm K} (isometry : form.Isometry)
    (left right : Coordinates3.Vector K) :
    form.bilinear ((act isometry) left)
      ((act isometry) right) =
      form.bilinear left right := by
  calc
    form.bilinear ((act isometry) left)
      ((act isometry) right) =
        Coordinates3.Vector.dot
          (Matrix3.rowMul
            (Matrix3.rowMul left isometry.matrix) form.matrix)
          (Matrix3.rowMul right isometry.matrix) := rfl
    _ = Coordinates3.Vector.dot (Matrix3.rowMul right isometry.matrix)
        (Matrix3.rowMul
          (Matrix3.rowMul left isometry.matrix) form.matrix) :=
      Coordinates3.Vector.dot_comm _ _
    _ = Coordinates3.Vector.dot right
        (Matrix3.rowMul
          (Matrix3.rowMul
            (Matrix3.rowMul left isometry.matrix) form.matrix)
          (Matrix3.transpose isometry.matrix)) :=
      Matrix3.dot_rowMul_transpose right
        (Matrix3.rowMul
          (Matrix3.rowMul left isometry.matrix) form.matrix)
        isometry.matrix
    _ = Coordinates3.Vector.dot right
        (Matrix3.rowMul left
          (Matrix3.mul
            (Matrix3.mul isometry.matrix form.matrix)
            (Matrix3.transpose isometry.matrix))) := by
      rw [Matrix3.rowMul_mul, Matrix3.rowMul_mul]
      rw [Matrix3.mul_assoc]
    _ = Coordinates3.Vector.dot right (Matrix3.rowMul left form.matrix) := by
      rw [isometry.preservesMatrix]
    _ = form.bilinear left right := Coordinates3.Vector.dot_comm _ _

/-- The isometry preserves the quadrance of every row vector. -/
theorem quadrance_act {form :
  Ternary.Basic.TernaryForm K} (isometry : form.Isometry)
    (vector : Coordinates3.Vector K) :
    form.quadrance ((act isometry) vector) = form.quadrance
      vector := by
  unfold TernaryForm.quadrance
  exact (bilinear_act isometry) vector vector

/-- An isometry sends a vector with nonzero quadrance to another vector with nonzero quadrance. -/
theorem quadrance_act_ne_zero {form : Ternary.Basic.TernaryForm K} (isometry : form.Isometry)
    (vector : Coordinates3.Vector K) (nonNull : form.quadrance vector ≠ 0) :
    form.quadrance (act isometry vector) ≠ 0 :=
  fun zero => nonNull ((quadrance_act isometry vector).symm.trans zero)

/-- An isometry sends a null vector to a null vector. -/
theorem isNull_act {form :
  Ternary.Basic.TernaryForm K} (isometry : form.Isometry)
    {vector : Coordinates3.Vector K} (null : form.IsNull vector) :
    form.IsNull ((act isometry) vector) := by
  unfold TernaryForm.IsNull at null ⊢
  rw [(quadrance_act isometry), null]

/-- An isometry preserves perpendicularity of two vectors. -/
theorem perpendicular_act {form :
  Ternary.Basic.TernaryForm K} (isometry : form.Isometry)
    {left right : Coordinates3.Vector K} (perpendicular : form.Perpendicular left right) :
    form.Perpendicular ((act isometry) left)
      ((act isometry) right) := by
  unfold TernaryForm.Perpendicular at perpendicular ⊢
  rw [(bilinear_act isometry), perpendicular]

/-- The identity isometry, with no inferred inverse data. -/
def identity (form : Ternary.Basic.TernaryForm
  K) : form.Isometry where
  matrix := Matrix3.identity
  inverseMatrix := Matrix3.identity
  matrix_mul_inverse := Matrix3.identity_mul Matrix3.identity
  inverse_mul_matrix := Matrix3.identity_mul Matrix3.identity
  preservesMatrix := by
    rw [Matrix3.identity_mul, Matrix3.transpose_identity,
      Matrix3.mul_identity]

/-- Product of two form isometries in the row-action order. -/
def mul {form : Ternary.Basic.TernaryForm K}
  (left right : form.Isometry) :
    form.Isometry where
  matrix := Matrix3.mul left.matrix right.matrix
  inverseMatrix := Matrix3.mul right.inverseMatrix left.inverseMatrix
  matrix_mul_inverse := by
    calc
      Matrix3.mul (Matrix3.mul left.matrix right.matrix)
          (Matrix3.mul right.inverseMatrix left.inverseMatrix) =
        Matrix3.mul left.matrix
          (Matrix3.mul
            (Matrix3.mul right.matrix right.inverseMatrix)
            left.inverseMatrix) := by
          rw [Matrix3.mul_assoc, Matrix3.mul_assoc]
      _ = Matrix3.mul left.matrix
          (Matrix3.mul Matrix3.identity left.inverseMatrix) := by
        rw [right.matrix_mul_inverse]
      _ = Matrix3.identity := by
        rw [Matrix3.identity_mul, left.matrix_mul_inverse]
  inverse_mul_matrix := by
    calc
      Matrix3.mul (Matrix3.mul right.inverseMatrix left.inverseMatrix)
          (Matrix3.mul left.matrix right.matrix) =
        Matrix3.mul right.inverseMatrix
          (Matrix3.mul
            (Matrix3.mul left.inverseMatrix left.matrix) right.matrix) := by
          rw [Matrix3.mul_assoc, Matrix3.mul_assoc]
      _ = Matrix3.mul right.inverseMatrix
          (Matrix3.mul Matrix3.identity right.matrix) := by
        rw [left.inverse_mul_matrix]
      _ = Matrix3.identity := by
        rw [Matrix3.identity_mul, right.inverse_mul_matrix]
  preservesMatrix := by
    rw [Matrix3.transpose_mul]
    calc
      Matrix3.mul
          (Matrix3.mul (Matrix3.mul left.matrix right.matrix) form.matrix)
          (Matrix3.mul (Matrix3.transpose right.matrix)
            (Matrix3.transpose left.matrix)) =
        Matrix3.mul left.matrix
          (Matrix3.mul
            (Matrix3.mul
              (Matrix3.mul right.matrix form.matrix)
              (Matrix3.transpose right.matrix))
            (Matrix3.transpose left.matrix)) := by
          rw [Matrix3.mul_assoc, Matrix3.mul_assoc, Matrix3.mul_assoc,
            Matrix3.mul_assoc]
      _ = Matrix3.mul left.matrix
          (Matrix3.mul form.matrix (Matrix3.transpose left.matrix)) := by
        rw [right.preservesMatrix]
      _ = Matrix3.mul
          (Matrix3.mul left.matrix form.matrix)
          (Matrix3.transpose left.matrix) := by
        rw [Matrix3.mul_assoc]
      _ = form.matrix := left.preservesMatrix

/-- Inverse form isometry, using the inverse already cached in the input. -/
def inverse {form : Ternary.Basic.TernaryForm K}
  (isometry : form.Isometry) :
    form.Isometry where
  matrix := isometry.inverseMatrix
  inverseMatrix := isometry.matrix
  matrix_mul_inverse := isometry.inverse_mul_matrix
  inverse_mul_matrix := isometry.matrix_mul_inverse
  preservesMatrix := by
    calc
      Purelib.LinearAlgebra.Coordinates3.Matrix3.mul (Purelib.LinearAlgebra.Coordinates3.Matrix3.mul
        isometry.inverseMatrix form.matrix)
          (Matrix3.transpose isometry.inverseMatrix) =
        Purelib.LinearAlgebra.Coordinates3.Matrix3.mul
          (Purelib.LinearAlgebra.Coordinates3.Matrix3.mul isometry.inverseMatrix
            (Purelib.LinearAlgebra.Coordinates3.Matrix3.mul
              (Purelib.LinearAlgebra.Coordinates3.Matrix3.mul isometry.matrix form.matrix)
              (Matrix3.transpose isometry.matrix)))
          (Matrix3.transpose isometry.inverseMatrix) := by
            rw [isometry.preservesMatrix]
      _ = Purelib.LinearAlgebra.Coordinates3.Matrix3.mul
          (Purelib.LinearAlgebra.Coordinates3.Matrix3.mul
            (Purelib.LinearAlgebra.Coordinates3.Matrix3.mul isometry.inverseMatrix isometry.matrix) form.matrix)
          (Purelib.LinearAlgebra.Coordinates3.Matrix3.mul (Matrix3.transpose isometry.matrix)
            (Matrix3.transpose isometry.inverseMatrix)) := by
        ext <;> unfold Purelib.LinearAlgebra.Coordinates3.Matrix3.mul <;> ring1
      _ = Purelib.LinearAlgebra.Coordinates3.Matrix3.mul
          (Purelib.LinearAlgebra.Coordinates3.Matrix3.mul Matrix3.identity form.matrix)
          (Matrix3.transpose
            (Purelib.LinearAlgebra.Coordinates3.Matrix3.mul isometry.inverseMatrix isometry.matrix)) := by
        rw [Matrix3.transpose_mul, isometry.inverse_mul_matrix]
      _ = form.matrix := by
        rw [isometry.inverse_mul_matrix, Matrix3.transpose_identity,
          Matrix3.identity_mul, Matrix3.mul_identity]

/-- The identity isometry fixes each vector. -/
theorem act_identity (form :
  Ternary.Basic.TernaryForm K) (vector : Coordinates3.Vector K) :
    (act
      (identity form)) vector = vector := by
  unfold act
    identity
  rw [Matrix3.rowMul_identity]

/-- The product isometry acts first by the left factor, then by the right factor. -/
theorem act_mul {form :
  Ternary.Basic.TernaryForm K} (left right : form.Isometry)
    (vector : Coordinates3.Vector K) :
    (act
      (mul left right)) vector =
      (act right)
      ((act left) vector) := by
  unfold act
    mul
  rw [Matrix3.rowMul_mul]

/-- Applying the retained inverse after the forward isometry recovers the vector. -/
theorem act_inverse_left {form :
  Ternary.Basic.TernaryForm K} (isometry : form.Isometry)
    (vector : Coordinates3.Vector K) :
    (act
      (inverse isometry))
      ((act isometry) vector) = vector := by
  unfold act
    inverse
  rw [Matrix3.rowMul_mul, isometry.matrix_mul_inverse,
    Matrix3.rowMul_identity]

/-- Applying the forward isometry after the retained inverse recovers the vector. -/
theorem act_inverse_right {form :
  Ternary.Basic.TernaryForm K} (isometry : form.Isometry)
    (vector : Coordinates3.Vector K) :
    (act isometry)
      ((act
      (inverse isometry)) vector) = vector := by
  unfold act
    inverse
  rw [Matrix3.rowMul_mul, isometry.inverse_mul_matrix,
    Matrix3.rowMul_identity]

end Isometry

/-- A bilinear preservation law on all displayed vectors determines the matrix preservation certificate, proved by the
nine coordinate pairs. -/
theorem preservesMatrix_of_bilinear (form :
  Ternary.Basic.TernaryForm K)
    (matrix : Coordinates3.Matrix3 K)
    (preserves : ∀ left right : Coordinates3.Vector K,
      form.bilinear (Matrix3.rowMul left matrix)
          (Matrix3.rowMul right matrix) = form.bilinear left right) :
    Matrix3.mul (Matrix3.mul matrix form.matrix)
        (Matrix3.transpose matrix) = form.matrix := by
  let basisT : Coordinates3.Vector K := ⟨1, 0, 0⟩
  let basisR : Coordinates3.Vector K := ⟨0, 1, 0⟩
  let basisS : Coordinates3.Vector K := ⟨0, 0, 1⟩
  apply Matrix3.ext
  · simpa [TernaryForm.bilinear, basisT, Matrix3.rowMul, Matrix3.mul,
      Matrix3.transpose, Coordinates3.Vector.dot] using preserves basisT basisT
  · simpa [TernaryForm.bilinear, basisT, basisR, Matrix3.rowMul, Matrix3.mul,
      Matrix3.transpose, Coordinates3.Vector.dot] using preserves basisT basisR
  · simpa [TernaryForm.bilinear, basisT, basisS, Matrix3.rowMul, Matrix3.mul,
      Matrix3.transpose, Coordinates3.Vector.dot] using preserves basisT basisS
  · simpa [TernaryForm.bilinear, basisT, basisR, Matrix3.rowMul, Matrix3.mul,
      Matrix3.transpose, Coordinates3.Vector.dot] using preserves basisR basisT
  · simpa [TernaryForm.bilinear, basisR, Matrix3.rowMul, Matrix3.mul,
      Matrix3.transpose, Coordinates3.Vector.dot] using preserves basisR basisR
  · simpa [TernaryForm.bilinear, basisR, basisS, Matrix3.rowMul, Matrix3.mul,
      Matrix3.transpose, Coordinates3.Vector.dot] using preserves basisR basisS
  · simpa [TernaryForm.bilinear, basisT, basisS, Matrix3.rowMul, Matrix3.mul,
      Matrix3.transpose, Coordinates3.Vector.dot] using preserves basisS basisT
  · simpa [TernaryForm.bilinear, basisR, basisS, Matrix3.rowMul, Matrix3.mul,
      Matrix3.transpose, Coordinates3.Vector.dot] using preserves basisS basisR
  · simpa [TernaryForm.bilinear, basisS, Matrix3.rowMul, Matrix3.mul,
      Matrix3.transpose, Coordinates3.Vector.dot] using preserves basisS basisS
end TernaryForm

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

end
