module

public import Purelib.Data.Fin.Permutation
public import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic
import Purelib.LinearAlgebra.Matrix.Rectangular.Identity
import Purelib.Algebra.FiniteSum.Fin

/-!
# Finite row and column transpositions

The same original index involution acts on independently bounded rectangular
rows and columns. Product laws retain the original middle dimension and sums.
-/

public section

namespace Purelib.LinearAlgebra.Matrix.Permutation

open Purelib.LinearAlgebra.Matrix
open Purelib.Algebra
open Purelib.Data.Fin (swapZero swapZero_involutive swapZero_injective sumFin_swapZero)

variable {K : Type*}

/-- Swap two rows, retaining structural finite matrix data. -/
@[expose] def swapRows {rows columns : Nat} (matrix : Rectangular K (rows + 1) columns)
    (pivot : Fin (rows + 1)) : Rectangular K (rows + 1) columns :=
  Rectangular.ofFn fun row column =>
    matrix (swapZero pivot row) column

/-- Swap two columns. -/
@[expose] def swapColumns {rows columns : Nat} (matrix : Rectangular K rows (columns + 1))
    (pivot : Fin (columns + 1)) : Rectangular K rows (columns + 1) :=
  Rectangular.ofFn fun row column =>
    matrix row (swapZero pivot column)

/-- Read a row-swapped matrix at the transposed original row index. -/
@[simp] theorem swapRows_apply {rows columns : Nat} (matrix : Rectangular K (rows + 1) columns)
    (pivot row : Fin (rows + 1)) (column : Fin columns) :
    swapRows matrix pivot row column = matrix
      (swapZero pivot row) column :=
  Rectangular.ofFn_apply _ _ _

/-- Read a column-swapped matrix at the transposed original column index. -/
@[simp] theorem swapColumns_apply {rows columns : Nat} (matrix : Rectangular K rows (columns + 1))
    (pivot : Fin (columns + 1)) (row : Fin rows) (column : Fin (columns + 1)) :
    swapColumns matrix pivot row column = matrix row
      (swapZero pivot column) :=
  Rectangular.ofFn_apply _ _ _

/-- Swapping the same two rows twice restores the original matrix.

Each structural matrix entry reads the involutive transposition of its
original row while retaining the same column. -/
@[simp] theorem swapRows_involutive {rows columns : Nat}
    (matrix : Rectangular K (rows + 1) columns) (pivot : Fin (rows + 1)) :
    swapRows (swapRows matrix pivot)
      pivot = matrix := by
  apply Rectangular.ext
  intro row column
  rewrite [swapRows_apply,
    swapRows_apply,
    swapZero_involutive]
  exact Eq.refl _

/-- Swapping the same two columns twice restores the original matrix.

Each structural matrix entry reads the involutive transposition of its
original column while retaining the same row. -/
@[simp] theorem swapColumns_involutive {rows columns : Nat}
    (matrix : Rectangular K rows (columns + 1)) (pivot : Fin (columns + 1)) :
    swapColumns (swapColumns matrix
      pivot) pivot = matrix := by
  apply Rectangular.ext
  intro row column
  rewrite [swapColumns_apply,
    swapColumns_apply,
    swapZero_involutive]
  exact Eq.refl _

section

variable [CommRing K]

/-- Matching inner column and row transpositions leave a matrix product unchanged. -/
theorem mul_swapColumns_swapRows {rows middle columns : Nat}
    (left : Rectangular K rows (middle + 1)) (right : Rectangular K (middle + 1) columns)
    (pivot : Fin (middle + 1)) :
    Rectangular.mul (swapColumns left pivot)
        (swapRows right pivot) =
      Rectangular.mul left right := by
  apply Rectangular.ext
  intro row column
  rw [Rectangular.mul_at,
    Rectangular.mul_at]
  calc
    FiniteSum.Fin.sumFin (fun middle =>
        swapColumns left pivot row middle *
          swapRows right pivot middle column) =
        FiniteSum.Fin.sumFin (fun middle =>
          left row (swapZero pivot middle) *
            right (swapZero pivot middle) column) := by
      apply FiniteSum.Fin.sumFin_congr
      intro middle
      rw [swapColumns_apply,
        swapRows_apply]
    _ = FiniteSum.Fin.sumFin (fun middle =>
          left row middle * right middle column) :=
      sumFin_swapZero pivot
        (fun middle => left row middle * right middle column)

/-- Move an inner column transposition from the left factor to the rows of the right factor. -/
theorem mul_swapColumns_left {rows middle columns : Nat}
    (left : Rectangular K rows (middle + 1)) (right : Rectangular K (middle + 1) columns)
    (pivot : Fin (middle + 1)) :
    Rectangular.mul (swapColumns left pivot) right =
      Rectangular.mul left (swapRows right pivot) := by
  have cancellation := mul_swapColumns_swapRows left
    (swapRows right pivot) pivot
  simpa only [swapRows_involutive] using cancellation

/-- Move an inner row transposition from the right factor to the columns of the left factor. -/
theorem mul_swapRows_right {rows middle columns : Nat}
    (left : Rectangular K rows (middle + 1)) (right : Rectangular K (middle + 1) columns)
    (pivot : Fin (middle + 1)) :
    Rectangular.mul left (swapRows right pivot) =
      Rectangular.mul (swapColumns left pivot) right :=
  (mul_swapColumns_left left right pivot).symm

/-- A column transposition of the right factor transposes the same columns of the product. -/
theorem mul_swapColumns_right {rows middle columns : Nat}
    (left : Rectangular K rows middle) (right : Rectangular K middle (columns + 1))
    (pivot : Fin (columns + 1)) :
    Rectangular.mul left (swapColumns right pivot) =
      swapColumns (Rectangular.mul left right) pivot := by
  apply Rectangular.ext
  intro row column
  rw [Rectangular.mul_at, swapColumns_apply,
    Rectangular.mul_at]
  apply FiniteSum.Fin.sumFin_congr
  intro middle
  rw [swapColumns_apply]

/-- A row transposition of the left factor transposes the same rows of the product. -/
theorem mul_swapRows_left {rows middle columns : Nat}
    (left : Rectangular K (rows + 1) middle) (right : Rectangular K middle columns)
    (pivot : Fin (rows + 1)) :
    Rectangular.mul (swapRows left pivot) right =
      swapRows (Rectangular.mul left right) pivot := by
  apply Rectangular.ext
  intro row column
  rw [Rectangular.mul_at, swapRows_apply,
    Rectangular.mul_at]
  apply FiniteSum.Fin.sumFin_congr
  intro middle
  rw [swapRows_apply]

/-- Matching row and column transpositions preserve a scalar identity matrix.

Equal retained coordinates remain equal after the same injective transposition.
Distinct coordinates remain distinct, so the same diagonal scalar is selected. -/
theorem swapRows_swapColumns_scaleIdentity {size : Nat}
    (scalar : K) (pivot : Fin (size + 1)) :
    swapRows
        (swapColumns
          (Multiplication.scaleIdentity scalar) pivot) pivot =
      Multiplication.scaleIdentity scalar := by
  apply Rectangular.ext
  intro row column
  rewrite [swapRows_apply,
    swapColumns_apply,
    Multiplication.scaleIdentity_apply, Multiplication.scaleIdentity_apply]
  by_cases equal : row = column
  · subst column
    rewrite [if_pos (Eq.refl _), if_pos (Eq.refl _)]
    exact Eq.refl _
  · rewrite [if_neg equal]
    rewrite [if_neg (fun swappedEqual =>
      equal (swapZero_injective pivot swappedEqual))]
    exact Eq.refl _

/-- Matching column and row transpositions preserve a scalar identity matrix.

The same injective transposition preserves the retained equality test for
the two finite coordinates, leaving every diagonal and off-diagonal entry intact. -/
theorem swapColumns_swapRows_scaleIdentity {size : Nat}
    (scalar : K) (pivot : Fin (size + 1)) :
    swapColumns
        (swapRows
          (Multiplication.scaleIdentity scalar) pivot) pivot =
      Multiplication.scaleIdentity scalar := by
  apply Rectangular.ext
  intro row column
  rewrite [swapColumns_apply,
    swapRows_apply,
    Multiplication.scaleIdentity_apply, Multiplication.scaleIdentity_apply]
  by_cases equal : row = column
  · subst column
    rewrite [if_pos (Eq.refl _), if_pos (Eq.refl _)]
    exact Eq.refl _
  · rewrite [if_neg equal]
    rewrite [if_neg (fun swappedEqual =>
      equal (swapZero_injective pivot swappedEqual))]
    exact Eq.refl _

/-- Move one displayed entry to the upper-left corner. -/
@[expose] def pivotMatrix {rows columns : Nat}
    (matrix : Rectangular K (rows + 1) (columns + 1))
    (rowPivot : Fin (rows + 1)) (columnPivot : Fin (columns + 1)) :
    Rectangular K (rows + 1) (columns + 1) :=
  swapColumns (swapRows matrix
    rowPivot) columnPivot

/-- Retain the original identity with its two displayed rows transposed. -/
@[expose] def matrix {dimension : Nat} (pivot : Fin (dimension + 1)) :
    Rectangular K (dimension + 1) (dimension + 1) :=
  swapRows (Multiplication.scaleIdentity 1) pivot

/-- Left multiplication by a retained transposition reads the same transposed original rows. -/
theorem matrix_mul {rows columns : Nat} (pivot : Fin (rows + 1))
    (original : Rectangular K (rows + 1) columns) :
    Rectangular.mul (matrix pivot) original = swapRows original pivot := by
  rw [matrix, mul_swapRows_left, Rectangular.unit_mul]

/-- Right multiplication by a retained transposition reads the same transposed original columns. -/
theorem mul_matrix {rows columns : Nat} (original : Rectangular K rows (columns + 1))
    (pivot : Fin (columns + 1)) :
    Rectangular.mul original (matrix pivot) = swapColumns original pivot := by
  rw [matrix, mul_swapRows_right, Rectangular.mul_unit]

/-- A retained row transposition is its own inverse at the same original dimension. -/
theorem matrix_mul_self {dimension : Nat} (pivot : Fin (dimension + 1)) :
    Rectangular.mul (matrix (K := K) pivot) (matrix pivot) = Multiplication.scaleIdentity 1 := by
  rw [matrix_mul, matrix, swapRows_involutive]

/-- The same original transposition matrix supplies both actual inverse identities. -/
@[expose] def inverse {dimension : Nat} (pivot : Fin (dimension + 1)) :
    Inverse.Scaled.Basic.ScaledInverse (matrix (K := K) pivot) where
  scalar := 1
  inverse := matrix pivot
  left_identity := matrix_mul_self pivot
  right_identity := matrix_mul_self pivot

/-- Pivoting a rectangle is the actual product with its two retained transposition matrices. -/
theorem pivotMatrix_eq_mul {rows columns : Nat}
    (original : Rectangular K (rows + 1) (columns + 1))
    (rowPivot : Fin (rows + 1)) (columnPivot : Fin (columns + 1)) :
    pivotMatrix original rowPivot columnPivot =
      Rectangular.mul (Rectangular.mul (matrix rowPivot) original) (matrix columnPivot) := by
  rw [matrix_mul, mul_matrix]
  rfl

end

end Purelib.LinearAlgebra.Matrix.Permutation

end
