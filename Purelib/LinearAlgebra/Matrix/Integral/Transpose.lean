module
import Purelib.Data.Fin.Two
import Purelib.Data.Int.Arithmetic

import Purelib.Algebra.FiniteSum.Fin
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Integral.Two
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.LinearAlgebra.Vector.Dot
import Mathlib.Tactic.Linter.Lint
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring

/-!
# Integral transposes and finite evaluation

The transpose moves an integral matrix action between the two arguments of
finite coordinate evaluation. This fixes the dual action on an evaluation
column in every finite dimension, independently of a geometric realization.
-/

public section

namespace Purelib.LinearAlgebra.Matrix.Integral.Transpose

open Purelib
open Purelib.Data.Int
open Purelib.Algebra.FiniteSum.Fin
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.Matrix

/-- Transpose an integral structural matrix in its original finite dimension.

Rows and columns exchange while retaining the same finite coordinate type. -/
@[expose] def transpose {dimension : Nat} (matrix : SquareMatrix Int dimension) : SquareMatrix Int dimension :=
  matrixOfFn fun row column => matrix column row

/-- Read a transposed entry by exchanging its row and column indices. -/
@[simp] theorem transpose_apply {dimension : Nat} (matrix : SquareMatrix Int dimension)
    (row column : Fin dimension) : transpose matrix row column = matrix column row :=
  matrixOfFn_apply _ _ _

/-- Transpose a displayed two-by-two matrix by exchanging its off-diagonal entries. -/
@[simp] theorem transpose_matrix₂ (a b c d :
  Int) :
    transpose (Two.matrix₂ a b c d) =
      Two.matrix₂ a c b d := by
  apply matrix_ext
  intro row column
  rcases Data.Fin.Two.finTwo_cases row with rowZero | rowOne <;>
    rcases Data.Fin.Two.finTwo_cases column with columnZero | columnOne <;>
    subst row <;> subst column <;> rfl

/-- Transposing twice restores the original integral matrix. -/
@[simp] theorem transpose_transpose {dimension : Nat} (matrix : SquareMatrix Int dimension) :
    transpose (transpose matrix) = matrix := by
  apply matrix_ext
  intro row column
  rw [transpose_apply, transpose_apply]

/-- Transposing the integral identity matrix leaves it unchanged. -/
@[simp] theorem transpose_identity {dimension : Nat} :
    transpose (Multiplication.identity :
      SquareMatrix Int dimension) = Multiplication.identity := by
  apply matrix_ext
  intro row column
  rw [transpose_apply]
  unfold Multiplication.identity
  rw [matrixOfFn_apply, matrixOfFn_apply]
  by_cases equal : row = column
  · subst column
    rfl
  · rw [if_neg equal, if_neg (Ne.symm equal)]

/-- Transposing an integral matrix product reverses the order of the transposed factors. -/
theorem transpose_mul {dimension : Nat} (left right : SquareMatrix Int dimension) :
    transpose (Multiplication.mul left right) =
      Multiplication.mul (transpose right)
      (transpose left) := by
  apply matrix_ext
  intro row column
  rw [transpose_apply, Multiplication.mul_apply, Multiplication.mul_apply]
  apply sumFin_congr
  intro middle
  rw [transpose_apply, transpose_apply]
  exact Arithmetic.mul_comm _ _

/-- Acting by a transpose on a coordinate column equals right multiplication of its evaluation row.

Each output entry pairs the same evaluation coefficients with one column
of the original matrix. The proof uses scalar commutativity at each finite
index, without equating functions under a binder. -/
theorem matrixVector_transpose {dimension : Nat} (matrix : SquareMatrix Int dimension)
    (evaluations : Data.Vector Int dimension) :
    Multiplication.matrixVector (transpose matrix) evaluations =
      Multiplication.vectorMatrix evaluations matrix := by
  apply Data.Vector.Basic.vector_ext
  intro coordinate
  rw [Multiplication.matrixVector_apply, Multiplication.vectorMatrix_apply]
  apply sumFin_congr
  intro middle
  rw [transpose_apply]
  exact Arithmetic.mul_comm _ _

/-- Transposed evaluation coefficients pair with a cycle exactly as the original coefficients pair with its image.

This finite evaluation law determines the dual matrix from the action on
cycle-coordinate columns. It asserts no geometric transport or integral
comparison by itself. -/
theorem dot_transpose_matrixVector {dimension : Nat} (matrix : SquareMatrix Int dimension)
    (evaluations cycle : Data.Vector Int dimension) :
    LinearAlgebra.Vector.Dot.dot (Multiplication.matrixVector (transpose matrix) evaluations) cycle =
      LinearAlgebra.Vector.Dot.dot evaluations (Multiplication.matrixVector matrix cycle) := by
  rw [matrixVector_transpose]
  exact Multiplication.dot_vectorMatrix_matrixVector evaluations matrix cycle

end Purelib.LinearAlgebra.Matrix.Integral.Transpose
