module
import Purelib.Data.Fin.Two

import Purelib.Algebra.FiniteSum.Fin
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Integral.Two
import Purelib.LinearAlgebra.Matrix.Multiplication
import Mathlib.Tactic.Linter.Lint
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

section
@[expose] public section

/-!
# Finite genus-one Picard--Lefschetz action

This module evaluates the two adjacent three-strand Artin generators as
explicit integral maps on the displayed genus-one cellular homology.  The
action is folded in the path order locked by `LegendreConventions`; no braid
quotient or remembered analytic monodromy matrix is used.
-/

namespace Purelib.LinearAlgebra.Matrix.Integral.Transpose

/-! ## The dual action on period columns -/

/-- Transpose a two-by-two integral structural matrix.

Rows and columns exchange while retaining the same finite coordinate type. -/
def transpose (matrix :
  LinearAlgebra.Matrix.Basic.IntegralMatrix) : LinearAlgebra.Matrix.Basic.IntegralMatrix :=
  SquareMatrix.matrixOfFn fun row column => matrix column row

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
/-- Read a transposed entry by exchanging its row and column indices. -/
@[simp] theorem transpose_apply (matrix :
  LinearAlgebra.Matrix.Basic.IntegralMatrix)
    (row column : Fin 2) : SquareMatrix.Integral.Transpose.transpose matrix row column = matrix column row :=
  SquareMatrix.matrixOfFn_apply _ _ _

/-- Transpose a displayed two-by-two matrix by exchanging its off-diagonal entries. -/
@[simp] theorem transpose_matrix₂ (a b c d :
  Int) :
    SquareMatrix.Integral.Transpose.transpose (SquareMatrix.Integral.Two.matrix₂ a b c d) =
      SquareMatrix.Integral.Two.matrix₂ a c b d := open Purelib in by
  apply SquareMatrix.matrix_ext
  intro row column
  rcases Data.Fin.Two.finTwo_cases row with rowZero | rowOne <;>
    rcases Data.Fin.Two.finTwo_cases column with columnZero | columnOne <;>
    subst row <;> subst column <;> rfl

/-- Transposing twice restores the original integral matrix. -/
@[simp] theorem transpose_transpose (matrix :
  LinearAlgebra.Matrix.Basic.IntegralMatrix) :
    SquareMatrix.Integral.Transpose.transpose (SquareMatrix.Integral.Transpose.transpose matrix) = matrix := by
  apply SquareMatrix.matrix_ext
  intro row column
  rw [SquareMatrix.Integral.Transpose.transpose_apply, SquareMatrix.Integral.Transpose.transpose_apply]

/-- Transposing the integral identity matrix leaves it unchanged. -/
@[simp] theorem transpose_identity :
    SquareMatrix.Integral.Transpose.transpose (SquareMatrix.Multiplication.identity :
      LinearAlgebra.Matrix.Basic.IntegralMatrix) = SquareMatrix.Multiplication.identity := by
  apply SquareMatrix.matrix_ext
  intro row column
  rw [SquareMatrix.Integral.Transpose.transpose_apply]
  unfold SquareMatrix.Multiplication.identity
  rw [SquareMatrix.matrixOfFn_apply, SquareMatrix.matrixOfFn_apply]
  by_cases equal : row = column
  · subst column
    rfl
  · rw [if_neg equal, if_neg (Ne.symm equal)]

/-- Transposing an integral matrix product reverses the order of the transposed factors. -/
theorem transpose_mul (left right :
  LinearAlgebra.Matrix.Basic.IntegralMatrix) :
    SquareMatrix.Integral.Transpose.transpose (SquareMatrix.Multiplication.mul left right) =
      SquareMatrix.Multiplication.mul (SquareMatrix.Integral.Transpose.transpose right)
      (SquareMatrix.Integral.Transpose.transpose left) := open Purelib.Algebra in by
  apply SquareMatrix.matrix_ext
  intro row column
  rw [SquareMatrix.Integral.Transpose.transpose_apply, SquareMatrix.Multiplication.mul_apply,
    SquareMatrix.Multiplication.mul_apply, FiniteSum.Fin.sumFin_two_int, FiniteSum.Fin.sumFin_two_int]
  simp only [SquareMatrix.Integral.Transpose.transpose_apply]
  ring1
end Purelib.LinearAlgebra.Matrix.Integral.Transpose

end
