module

public import Purelib.Algebra.FiniteSum.Fin
public import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Data.Fin
import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring

/-!
# Original finite tensor matrix and vector operations

Row-major product indices retain both original bounded components. Each
constructor materializes its index table once before building entries. Tensor
product and tensor sum actions retain both input matrices and vectors in their
pointwise laws, including arbitrary nonzero residuals.
-/

public section

namespace Purelib.LinearAlgebra.Matrix.Tensor

open Purelib
open Purelib.Algebra.FiniteSum
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

variable {K : Type*} [CommRing K] {leftSize rightSize : Nat}

/-- Materialize both original bounded product components once at every row-major position. -/
private def indices (leftSize rightSize : Nat) :
    Data.Vector (Fin leftSize × Fin rightSize) (leftSize * rightSize) :=
  vectorOfFn fun index => ((Data.Fin.divNat index), (Data.Fin.modNat index))

/-- Materialize the tensor product of the two original finite vectors. -/
def vector (first : Data.Vector K leftSize) (second : Data.Vector K rightSize) :
    Data.Vector K (leftSize * rightSize) :=
  let positions := indices leftSize rightSize
  vectorOfFn fun index => first (positions index).1 * second (positions index).2

/-- Read one tensor-vector component at its same original bounded pair. -/
theorem vector_apply (first : Data.Vector K leftSize) (second : Data.Vector K rightSize)
    (index : Fin (leftSize * rightSize)) :
      vector first second index =
        first (Data.Fin.divNat index) * second (Data.Fin.modNat index) := by
  unfold vector indices
  rewrite [vectorOfFn_apply, vectorOfFn_apply]
  rfl

/-- Read the tensor-vector component at a pair of actual original indices. -/
theorem vector_pair (first : Data.Vector K leftSize) (second : Data.Vector K rightSize)
    (left : Fin leftSize) (right : Fin rightSize) :
    vector first second (Fin.mkDivMod left right) = first left * second right := by
  rewrite [vector_apply, Data.Fin.divNat_mkDivMod, Data.Fin.modNat_mkDivMod]
  rfl

/-- Construct the tensor product of two original structural matrices using their cached bounded product positions. -/
def product (first : SquareMatrix K leftSize) (second : SquareMatrix K rightSize) :
    SquareMatrix K (leftSize * rightSize) :=
  let positions := indices leftSize rightSize
  SquareMatrix.matrixOfFn fun row column =>
    first (positions row).1 (positions column).1 * second (positions row).2 (positions column).2

/-- Each tensor-matrix entry reads its same original row and column pairs. -/
theorem product_apply (first : SquareMatrix K leftSize) (second : SquareMatrix K rightSize)
    (row column : Fin (leftSize * rightSize)) :
    product first second row column =
      first (Data.Fin.divNat row) (Data.Fin.divNat column) * second (Data.Fin.modNat row) (Data.Fin.modNat column) := by
  unfold product indices
  rewrite [SquareMatrix.matrixOfFn_apply, vectorOfFn_apply, vectorOfFn_apply]
  rfl

/-- The original tensor product acts by the product of both original matrix-vector actions. -/
theorem product_action (first : SquareMatrix K leftSize) (second : SquareMatrix K rightSize)
    (left : Data.Vector K leftSize) (right : Data.Vector K rightSize) (row : Fin (leftSize * rightSize)) :
    SquareMatrix.Multiplication.matrixVector (product first second) (vector left right) row =
      SquareMatrix.Multiplication.matrixVector first left (Data.Fin.divNat row) *
        SquareMatrix.Multiplication.matrixVector second right (Data.Fin.modNat row) := by
  rewrite [SquareMatrix.Multiplication.matrixVector_apply, Fin.sumFin_product]
  calc
    _ = Fin.sumFin (fun column : Fin leftSize => Fin.sumFin (fun entry : Fin rightSize =>
        (first (Data.Fin.divNat row) column * left column) * (second (Data.Fin.modNat row) entry * right entry))) := by
      apply Fin.sumFin_congr
      intro column
      apply Fin.sumFin_congr
      intro entry
      rewrite [product_apply, vector_pair, Data.Fin.divNat_mkDivMod, Data.Fin.modNat_mkDivMod]
      ring0
    _ = Fin.sumFin (fun column : Fin leftSize => (first (Data.Fin.divNat row) column * left column) *
        Fin.sumFin (fun entry : Fin rightSize => second (Data.Fin.modNat row) entry * right entry)) := by
      apply Fin.sumFin_congr
      intro column
      exact Fin.sumFin_mul_left _ _
    _ = _ := by
      rewrite [Fin.sumFin_mul_right, SquareMatrix.Multiplication.matrixVector_apply,
        SquareMatrix.Multiplication.matrixVector_apply]
      rfl

/-- Construct the tensor sum using the same original matrices and their finite identity factors. -/
def sum (first : SquareMatrix K leftSize) (second : SquareMatrix K rightSize) :
    SquareMatrix K (leftSize * rightSize) :=
  let left := product first (SquareMatrix.Multiplication.scaleIdentity (n := rightSize) 1)
  let right := product (SquareMatrix.Multiplication.scaleIdentity (n := leftSize) 1) second
  SquareMatrix.add left right

/-- The original tensor sum retains both original matrix-vector actions and both unchanged vector factors. -/
theorem sum_action (first : SquareMatrix K leftSize) (second : SquareMatrix K rightSize)
    (left : Data.Vector K leftSize) (right : Data.Vector K rightSize) (row : Fin (leftSize * rightSize)) :
    SquareMatrix.Multiplication.matrixVector (sum first second) (vector left right) row =
      SquareMatrix.Multiplication.matrixVector first left (Data.Fin.divNat row) * right (Data.Fin.modNat row) +
        left (Data.Fin.divNat row) * SquareMatrix.Multiplication.matrixVector second right (Data.Fin.modNat row) := by
  unfold sum
  rewrite [SquareMatrix.Multiplication.matrixVector_add, product_action, product_action,
    SquareMatrix.Multiplication.matrixVector_scaleIdentity, vectorOfFn_apply,
    SquareMatrix.Multiplication.matrixVector_scaleIdentity, vectorOfFn_apply, one_mul, one_mul]
  rfl

/-- Two original eigenvectors give an eigenvector for the product of their original eigenvalues. -/
theorem product_eigenvector (first : SquareMatrix K leftSize) (second : SquareMatrix K rightSize)
    (left : Data.Vector K leftSize) (right : Data.Vector K rightSize) (leftValue rightValue : K)
    (leftEigen : ∀ row, SquareMatrix.Multiplication.matrixVector first left row = leftValue * left row)
    (rightEigen : ∀ row, SquareMatrix.Multiplication.matrixVector second right row = rightValue * right row)
    (row : Fin (leftSize * rightSize)) :
    SquareMatrix.Multiplication.matrixVector (product first second) (vector left right) row =
      (leftValue * rightValue) * vector left right row := by
  rewrite [product_action, leftEigen (Data.Fin.divNat row), rightEigen (Data.Fin.modNat row), vector_apply]
  ring0

/-- Two original eigenvectors give an eigenvector for the sum of their original eigenvalues. -/
theorem sum_eigenvector (first : SquareMatrix K leftSize) (second : SquareMatrix K rightSize)
    (left : Data.Vector K leftSize) (right : Data.Vector K rightSize) (leftValue rightValue : K)
    (leftEigen : ∀ row, SquareMatrix.Multiplication.matrixVector first left row = leftValue * left row)
    (rightEigen : ∀ row, SquareMatrix.Multiplication.matrixVector second right row = rightValue * right row)
    (row : Fin (leftSize * rightSize)) :
    SquareMatrix.Multiplication.matrixVector (sum first second) (vector left right) row =
      (leftValue + rightValue) * vector left right row := by
  rewrite [sum_action, leftEigen (Data.Fin.divNat row), rightEigen (Data.Fin.modNat row), vector_apply]
  ring0

end Purelib.LinearAlgebra.Matrix.Tensor

end
