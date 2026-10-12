module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Blocks
public import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.LinearAlgebra.Vector.Dot
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

open Purelib.LinearAlgebra.Vector

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

namespace Purelib.LinearAlgebra.Matrix.Schur

universe u
variable {K : Type*} [CommRing K]

/-- Compute the fraction-free Schur complement at the leading matrix entry.

Each tail entry is multiplied by that pivot and corrected by the corresponding column-row product. -/
def schur (matrix : SquareMatrix K (n + 1)) : SquareMatrix
  K n :=
  SquareMatrix.matrixOfFn fun row column =>
    SquareMatrix.Blocks.head matrix * SquareMatrix.Blocks.tail matrix row column -
      SquareMatrix.Blocks.leftColumn matrix row * SquareMatrix.Blocks.topRow matrix column

/-- The Schur matrix evaluated at one displayed entry. -/
theorem schur_apply {n : Nat} (matrix : SquareMatrix K (n
  + 1))
    (row column : Fin n) :
    SquareMatrix.Schur.schur matrix row column =
      SquareMatrix.Blocks.head matrix * SquareMatrix.Blocks.tail matrix row column -
        SquareMatrix.Blocks.leftColumn matrix row * SquareMatrix.Blocks.topRow matrix column := by
  unfold SquareMatrix.Schur.schur
  rw [SquareMatrix.matrixOfFn_apply]

/-- Express the Schur complement action as a scaled tail action minus the column correction. -/
theorem matrixVector_schur {n : Nat} (matrix :
  SquareMatrix K (n + 1))
    (vector : Data.Vector K n) (row : Fin n) :
    SquareMatrix.Multiplication.matrixVector (SquareMatrix.Schur.schur matrix) vector row =
      SquareMatrix.Blocks.head matrix * SquareMatrix.Multiplication.matrixVector (SquareMatrix.Blocks.tail matrix)
        vector row -
        SquareMatrix.Blocks.leftColumn matrix row * Dot.dot (SquareMatrix.Blocks.topRow matrix) vector := open
          Purelib.Algebra in by
  calc
    SquareMatrix.Multiplication.matrixVector (SquareMatrix.Schur.schur matrix) vector row =
        FiniteSum.Fin.sumFin (fun i => SquareMatrix.Schur.schur matrix row i * vector i) :=
      SquareMatrix.Multiplication.matrixVector_apply (SquareMatrix.Schur.schur matrix) vector row
    _ = FiniteSum.Fin.sumFin (fun i =>
        (SquareMatrix.Blocks.head matrix * SquareMatrix.Blocks.tail matrix row i -
          SquareMatrix.Blocks.leftColumn matrix row * SquareMatrix.Blocks.topRow matrix i) * vector i) :=
      FiniteSum.Fin.sumFin_congr (fun i =>
        congrArg (fun entry => entry * vector i)
          (SquareMatrix.Schur.schur_apply matrix row i))
    _ = FiniteSum.Fin.sumFin (fun i => SquareMatrix.Blocks.head matrix * SquareMatrix.Blocks.tail matrix row i * vector
      i -
        SquareMatrix.Blocks.leftColumn matrix row * SquareMatrix.Blocks.topRow matrix i * vector i) :=
      FiniteSum.Fin.sumFin_congr (fun _ => by ring1)
    _ = FiniteSum.Fin.sumFin (fun i => SquareMatrix.Blocks.head matrix * SquareMatrix.Blocks.tail matrix row i * vector
      i) -
        FiniteSum.Fin.sumFin (fun i =>
          SquareMatrix.Blocks.leftColumn matrix row * SquareMatrix.Blocks.topRow matrix i * vector i) :=
      FiniteSum.Fin.sumFin_sub _ _
    _ = FiniteSum.Fin.sumFin (fun i => SquareMatrix.Blocks.head matrix *
          (SquareMatrix.Blocks.tail matrix row i * vector i)) -
        FiniteSum.Fin.sumFin (fun i => SquareMatrix.Blocks.leftColumn matrix row *
          (SquareMatrix.Blocks.topRow matrix i * vector i)) :=
      congrArg₂ (fun left right => left - right)
        (FiniteSum.Fin.sumFin_congr (fun _ => by ring1))
        (FiniteSum.Fin.sumFin_congr (fun _ => by ring1))
    _ = SquareMatrix.Blocks.head matrix * FiniteSum.Fin.sumFin (fun i => SquareMatrix.Blocks.tail matrix row i * vector
      i) -
        SquareMatrix.Blocks.leftColumn matrix row *
          FiniteSum.Fin.sumFin (fun i => SquareMatrix.Blocks.topRow matrix i * vector i) := by
      rw [FiniteSum.Fin.sumFin_mul_left, FiniteSum.Fin.sumFin_mul_left]
    _ = SquareMatrix.Blocks.head matrix * SquareMatrix.Multiplication.matrixVector (SquareMatrix.Blocks.tail matrix)
      vector row -
        SquareMatrix.Blocks.leftColumn matrix row * Dot.dot (SquareMatrix.Blocks.topRow matrix) vector := by
      rw [SquareMatrix.Multiplication.matrixVector_apply]
      unfold Dot.dot
      rfl

/-- Express the row-vector Schur action as a scaled tail action minus the row correction. -/
theorem vectorMatrix_schur {n : Nat} (vector :
  Data.Vector K n)
    (matrix : SquareMatrix K (n + 1)) (column : Fin n) :
    SquareMatrix.Multiplication.vectorMatrix vector (SquareMatrix.Schur.schur matrix) column =
      SquareMatrix.Blocks.head matrix * SquareMatrix.Multiplication.vectorMatrix vector (SquareMatrix.Blocks.tail
        matrix) column -
        Dot.dot vector (SquareMatrix.Blocks.leftColumn matrix) * SquareMatrix.Blocks.topRow matrix column := open
          Purelib.Algebra in by
  unfold SquareMatrix.Multiplication.vectorMatrix
  rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
  unfold Dot.dot
  have tailColumn :
      FiniteSum.Fin.sumFin (fun i => vector i *
          Data.Vector.Basic.vectorOfFn (fun row => SquareMatrix.Blocks.tail matrix row column) i) =
        FiniteSum.Fin.sumFin (fun i => vector i * SquareMatrix.Blocks.tail matrix i column) :=
    FiniteSum.Fin.sumFin_congr (fun i => by rw [Data.Vector.Basic.vectorOfFn_apply])
  rw [tailColumn]
  rw [FiniteSum.Fin.sumFin_congr
    (right := fun i => vector i *
      (SquareMatrix.Blocks.head matrix * SquareMatrix.Blocks.tail matrix i column -
        SquareMatrix.Blocks.leftColumn matrix i * SquareMatrix.Blocks.topRow matrix column))
    (fun i => by
      rw [Data.Vector.Basic.vectorOfFn_apply]
      unfold SquareMatrix.Schur.schur
      rw [SquareMatrix.matrixOfFn_apply])]
  calc
    FiniteSum.Fin.sumFin (fun i => vector i *
        (SquareMatrix.Blocks.head matrix * SquareMatrix.Blocks.tail matrix i column -
          SquareMatrix.Blocks.leftColumn matrix i * SquareMatrix.Blocks.topRow matrix column)) =
      FiniteSum.Fin.sumFin (fun i => vector i * (SquareMatrix.Blocks.head matrix * SquareMatrix.Blocks.tail matrix i
        column) -
        vector i * (SquareMatrix.Blocks.leftColumn matrix i * SquareMatrix.Blocks.topRow matrix column)) :=
      FiniteSum.Fin.sumFin_congr (fun _ => by ring1)
    _ = FiniteSum.Fin.sumFin (fun i => vector i *
          (SquareMatrix.Blocks.head matrix * SquareMatrix.Blocks.tail matrix i column)) -
        FiniteSum.Fin.sumFin (fun i => vector i *
          (SquareMatrix.Blocks.leftColumn matrix i * SquareMatrix.Blocks.topRow matrix column)) :=
      FiniteSum.Fin.sumFin_sub _ _
    _ = FiniteSum.Fin.sumFin (fun i => SquareMatrix.Blocks.head matrix *
          (vector i * SquareMatrix.Blocks.tail matrix i column)) -
        FiniteSum.Fin.sumFin (fun i => (vector i * SquareMatrix.Blocks.leftColumn matrix i) *
          SquareMatrix.Blocks.topRow matrix column) :=
      congrArg₂ (fun left right => left - right)
        (FiniteSum.Fin.sumFin_congr (fun _ => by ring1))
        (FiniteSum.Fin.sumFin_congr (fun _ => by ring1))
    _ = SquareMatrix.Blocks.head matrix *
          FiniteSum.Fin.sumFin (fun i => vector i * SquareMatrix.Blocks.tail matrix i column) -
        FiniteSum.Fin.sumFin (fun i => vector i * SquareMatrix.Blocks.leftColumn matrix i) *
          SquareMatrix.Blocks.topRow matrix column := by
      rw [FiniteSum.Fin.sumFin_mul_left, FiniteSum.Fin.sumFin_mul_right]
end Purelib.LinearAlgebra.Matrix.Schur

end
