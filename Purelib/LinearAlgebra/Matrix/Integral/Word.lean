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
  Basic.IntegralMatrix ->
  Basic.IntegralMatrix
  | [] => Multiplication.identity
  | matrix :: remaining =>
      Multiplication.mul (Word.matrixProduct
        remaining) matrix

/-- Concatenating traversal-order matrix lists applies the first list before
the second, so the second folded matrix occurs on the left. -/
theorem matrixProduct_append (first second : List
  Basic.IntegralMatrix) :
    matrixProduct (first ++ second) =
      Multiplication.mul
        (matrixProduct second) (matrixProduct first) := by
  induction first with
  | nil =>
      simp only [List.nil_append, matrixProduct]
      exact
        (Multiplication.mul_identity_int
          (matrixProduct second)).symm
  | cons matrix remaining inductionHypothesis =>
      simp only [List.cons_append, matrixProduct, inductionHypothesis]
      exact Multiplication.mul_assoc
        (matrixProduct second) (matrixProduct remaining) matrix

/-- Reverse a traversal list while transposing every matrix.  This is the
finite dual list forced by evaluating periods on the transported homology
basis. -/
def dualMatrices : List
  Basic.IntegralMatrix -> List
  Basic.IntegralMatrix
  | [] => []
  | matrix :: remaining =>
      Word.dualMatrices remaining ++
        [Transpose.transpose matrix]

/-- Folding the dual list gives exactly the transpose of the original folded
homology matrix.

The retained matrix list is reversed while transposing each matrix. Its multiplication order gives the transpose of the
original complete finite product. -/
theorem matrixProduct_dualMatrices (matrices :
  List Basic.IntegralMatrix) :
    matrixProduct (dualMatrices matrices) =
      Transpose.transpose
        (matrixProduct matrices) := by
  induction matrices with
  | nil =>
      simp only [dualMatrices, matrixProduct,
        Transpose.transpose_identity, -eq_self, -iff_self]
      rfl
  | cons matrix remaining inductionHypothesis =>
      rw [dualMatrices, matrixProduct_append, inductionHypothesis]
      simp only [matrixProduct,
        Multiplication.identity_mul_int]
      rw [Transpose.transpose_mul]
namespace FoldPreparations
end FoldPreparations
end Purelib.LinearAlgebra.Matrix.Integral.Word

end
