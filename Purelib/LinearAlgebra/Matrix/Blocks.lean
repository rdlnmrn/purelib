module
import Purelib.Data.Vector.Basic
public import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.Data.Fin

open Purelib

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

section
@[expose] public section

/-!
# Fraction-free finite matrix inversion

Vectors and matrices are dimension-indexed structural `Vector` data, exposed
through entry lookup, and every sum is a fold over `List.ofFn`.  A scaled
inverse records both multiplication identities.  The block extension below
is division-free: a pivot and a scaled inverse of its Schur complement produce
a scaled inverse of the whole matrix.
-/

namespace Purelib.LinearAlgebra.Matrix.Blocks

universe u
variable {K : Type*} [CommRing K]

/-- Read the leading entry of a nonempty square matrix. -/
def head (matrix : SquareMatrix K (n + 1)) : K := matrix
  0 0

/-- Materialize the first row after deleting its leading entry. -/
def topRow (matrix : SquareMatrix K (n + 1)) :
  Data.Vector K n :=
  Data.Vector.Basic.vectorOfFn fun column => matrix 0 column.succ

/-- Materialize the first column after deleting its leading entry. -/
def leftColumn (matrix : SquareMatrix K (n + 1)) :
  Data.Vector K n :=
  Data.Vector.Basic.vectorOfFn fun row => matrix row.succ 0

omit [CommRing K] in
/-- Read a retained top-row entry at the corresponding successor column. -/
@[simp] theorem topRow_apply (matrix : SquareMatrix K (n
  + 1))
    (column : Fin n) :
    SquareMatrix.Blocks.topRow matrix column = matrix 0 column.succ := by
  exact Data.Vector.Basic.vectorOfFn_apply _ _

omit [CommRing K] in
/-- Read a retained left-column entry at the corresponding successor row. -/
@[simp] theorem leftColumn_apply (matrix : SquareMatrix K
  (n + 1))
    (row : Fin n) :
    SquareMatrix.Blocks.leftColumn matrix row = matrix row.succ 0 := by
  exact Data.Vector.Basic.vectorOfFn_apply _ _

/-- Delete the leading row and column of a nonempty square matrix.

The smaller structural matrix retains entries at the original successor indices. -/
def tail (matrix : SquareMatrix K (n + 1)) : SquareMatrix
  K n :=
  SquareMatrix.matrixOfFn fun row column => matrix row.succ column.succ

omit [CommRing K] in
/-- Read a tail entry at the corresponding original successor row and column. -/
@[simp] theorem tail_apply (matrix : SquareMatrix K (n +
  1))
    (row column : Fin n) :
    SquareMatrix.Blocks.tail matrix row column = matrix row.succ column.succ := by
  exact SquareMatrix.matrixOfFn_apply _ _ _
end Purelib.LinearAlgebra.Matrix.Blocks

end

section
@[expose] public section

/-! Exact finite block reads for the square handle-coordinate inverse argument. -/
namespace Purelib.LinearAlgebra.Matrix.Blocks

variable {K : Type*} [CommRing K]

/-- Assemble four equally sized structural matrices into a square block matrix.

The finite sum indices distinguish the first and second blocks in both directions. -/
def block {n : Nat} (aa ab ba bb : SquareMatrix K n) :
  SquareMatrix K (n + n) :=
  SquareMatrix.matrixOfFn fun row column => Data.Fin.addCases
    (fun first => Data.Fin.addCases (fun last => aa first last) (fun last => ab first last) column)
    (fun first => Data.Fin.addCases (fun last => ba first last) (fun last => bb first last) column) row

omit [CommRing K] in
/-- Read an entry in the upper-left block of the assembled matrix. -/
theorem block_ll {n : Nat} (aa ab ba bb : SquareMatrix K
  n) (row column : Fin n) :
    SquareMatrix.Blocks.block aa ab ba bb (Fin.castAdd n row) (Fin.castAdd n column) = aa row column := by
  rw [SquareMatrix.Blocks.block, SquareMatrix.matrixOfFn_apply, Data.Fin.addCases_left, Data.Fin.addCases_left]

omit [CommRing K] in
/-- Read an entry in the upper-right block of the assembled matrix. -/
theorem block_lr {n : Nat} (aa ab ba bb : SquareMatrix K
  n) (row column : Fin n) :
    SquareMatrix.Blocks.block aa ab ba bb (Fin.castAdd n row) (Fin.natAdd n column) = ab row column := by
  rw [SquareMatrix.Blocks.block, SquareMatrix.matrixOfFn_apply, Data.Fin.addCases_left, Data.Fin.addCases_right]

omit [CommRing K] in
/-- Read an entry in the lower-left block of the assembled matrix. -/
theorem block_rl {n : Nat} (aa ab ba bb : SquareMatrix K
  n) (row column : Fin n) :
    SquareMatrix.Blocks.block aa ab ba bb (Fin.natAdd n row) (Fin.castAdd n column) = ba row column := by
  rw [SquareMatrix.Blocks.block, SquareMatrix.matrixOfFn_apply, Data.Fin.addCases_right, Data.Fin.addCases_left]

omit [CommRing K] in
/-- Read an entry in the lower-right block of the assembled matrix. -/
theorem block_rr {n : Nat} (aa ab ba bb : SquareMatrix K
  n) (row column : Fin n) :
    SquareMatrix.Blocks.block aa ab ba bb (Fin.natAdd n row) (Fin.natAdd n column) = bb row column := by
  rw [SquareMatrix.Blocks.block, SquareMatrix.matrixOfFn_apply, Data.Fin.addCases_right, Data.Fin.addCases_right]
end Purelib.LinearAlgebra.Matrix.Blocks

end
