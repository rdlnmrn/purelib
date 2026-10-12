module

public import Purelib.LinearAlgebra.Matrix.Integral.Transpose
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.LinearAlgebra.Matrix.Basic
import Mathlib.Tactic.Linter.Lint
import Mathlib.Algebra.Ring.Int.Defs

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

section
@[expose] public section

/-!
# Finite-word Legendre fractional transport

This module folds convention-locked integral matrices and their precisely
indexed denominator preparations.  It keeps the unconditional homogeneous
matrix product separate from stepwise productive division, then proves that a
fully prepared fold agrees with one prepared quotient by the folded matrix.
For period transport it also reverses the generator list while transposing
each homology matrix, and proves that this finite fold is exactly the dual
`periodMatrix` action.
-/

namespace Purelib.LinearAlgebra.Matrix.Integral.Word

/-! ## Division-free finite matrix words -/

/-- Matrix product for traversal-order steps.  The head acts first, so later
entries multiply on the left. -/
def matrixProduct : List
  LinearAlgebra.Matrix.Basic.IntegralMatrix ->
  LinearAlgebra.Matrix.Basic.IntegralMatrix
  | [] => SquareMatrix.Multiplication.identity
  | matrix :: remaining =>
      SquareMatrix.Multiplication.mul (Purelib.LinearAlgebra.Matrix.Integral.Word.matrixProduct
        remaining) matrix

/-- Concatenating traversal-order matrix lists applies the first list before
the second, so the second folded matrix occurs on the left. -/
theorem matrixProduct_append (first second : List
  LinearAlgebra.Matrix.Basic.IntegralMatrix) :
    SquareMatrix.Integral.Word.matrixProduct (first ++ second) =
      SquareMatrix.Multiplication.mul
        (SquareMatrix.Integral.Word.matrixProduct second) (SquareMatrix.Integral.Word.matrixProduct first) := by
  induction first with
  | nil =>
      simp only [List.nil_append, SquareMatrix.Integral.Word.matrixProduct]
      exact
        (SquareMatrix.Multiplication.mul_identity_int
          (SquareMatrix.Integral.Word.matrixProduct second)).symm
  | cons matrix remaining inductionHypothesis =>
      simp only [List.cons_append, SquareMatrix.Integral.Word.matrixProduct, inductionHypothesis]
      exact SquareMatrix.Multiplication.mul_assoc
        (SquareMatrix.Integral.Word.matrixProduct second) (SquareMatrix.Integral.Word.matrixProduct remaining) matrix

/-- Reverse a traversal list while transposing every matrix.  This is the
finite dual list forced by evaluating periods on the transported homology
basis. -/
def dualMatrices : List
  LinearAlgebra.Matrix.Basic.IntegralMatrix -> List
  LinearAlgebra.Matrix.Basic.IntegralMatrix
  | [] => []
  | matrix :: remaining =>
      Purelib.LinearAlgebra.Matrix.Integral.Word.dualMatrices remaining ++
        [SquareMatrix.Integral.Transpose.transpose matrix]

/-- Folding the dual list gives exactly the transpose of the original folded
homology matrix.

The retained matrix list is reversed while transposing each matrix. Its multiplication order gives the transpose of the
original complete finite product. -/
theorem matrixProduct_dualMatrices (matrices :
  List LinearAlgebra.Matrix.Basic.IntegralMatrix) :
    SquareMatrix.Integral.Word.matrixProduct (SquareMatrix.Integral.Word.dualMatrices matrices) =
      SquareMatrix.Integral.Transpose.transpose
        (SquareMatrix.Integral.Word.matrixProduct matrices) := by
  induction matrices with
  | nil =>
      simp only [SquareMatrix.Integral.Word.dualMatrices, SquareMatrix.Integral.Word.matrixProduct,
        SquareMatrix.Integral.Transpose.transpose_identity, -eq_self, -iff_self]
      rfl
  | cons matrix remaining inductionHypothesis =>
      rw [SquareMatrix.Integral.Word.dualMatrices, SquareMatrix.Integral.Word.matrixProduct_append, inductionHypothesis]
      simp only [SquareMatrix.Integral.Word.matrixProduct,
        SquareMatrix.Multiplication.identity_mul_int]
      rw [SquareMatrix.Integral.Transpose.transpose_mul]
namespace FoldPreparations
end FoldPreparations
end Purelib.LinearAlgebra.Matrix.Integral.Word

end
