module

public import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Construction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Tactic.Ring

/-!
# Lower triangular borders with a scalar tail

The original retained border joins a leading scalar, column and scalar identity
on its tail. Its product and explicit unit inverse use the same structural
matrix kernel and original inverse record.
-/

public section

namespace Purelib.LinearAlgebra.Matrix.Triangular

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Algebra.FiniteSum.Fin
open Purelib.LinearAlgebra.Matrix
open Inverse.Scaled.Basic

variable {K : Type*} [CommRing K] {dimension : Nat}

/-- Retain a leading scalar and column above a scalar identity tail. -/
@[expose] def lower (corner : K) (column : Vec K dimension) (diagonal : K) :
    Rectangular K (dimension + 1) (dimension + 1) :=
  Blocks.border corner (vectorOfFn fun _ => 0) column (Multiplication.scaleIdentity diagonal)

/-- The leading entry of a lower triangular border is its retained corner. -/
theorem lower_zero_zero (corner : K) (column : Vec K dimension) (diagonal : K) :
    lower corner column diagonal 0 0 = corner := rfl

/-- The leading row after the corner of a lower triangular border is zero. -/
theorem lower_zero_succ (corner : K) (column : Vec K dimension) (diagonal : K)
    (index : Fin dimension) : lower corner column diagonal 0 index.succ = 0 :=
  vectorOfFn_apply _ _

/-- The leading column after the corner retains the original supplied column. -/
theorem lower_succ_zero (corner : K) (column : Vec K dimension) (diagonal : K)
    (index : Fin dimension) : lower corner column diagonal index.succ 0 = column index :=
  Blocks.border_succ_zero _ _ _ _ _

/-- The lower triangular tail reads the original scalar identity entry. -/
theorem lower_succ_succ (corner : K) (column : Vec K dimension) (diagonal : K)
    (row last : Fin dimension) :
    lower corner column diagonal row.succ last.succ = Multiplication.scaleIdentity diagonal row last :=
  Blocks.border_succ_succ _ _ _ _ _ _

/-- A lower triangular border with identity scalars and zero column is the original identity. -/
theorem lower_unit : lower (1 : K) (vectorOfFn (n := dimension) fun _ => 0) 1 =
    Multiplication.scaleIdentity 1 := Blocks.diagonal_unit dimension

/-- Multiply lower triangular borders using the original two columns and scalars. -/
theorem lower_mul (firstCorner secondCorner firstDiagonal secondDiagonal : K)
    (firstColumn secondColumn : Vec K dimension) :
    Rectangular.mul (lower firstCorner firstColumn firstDiagonal)
        (lower secondCorner secondColumn secondDiagonal) =
      lower (firstCorner * secondCorner)
        (vectorOfFn fun index => firstColumn index * secondCorner + firstDiagonal * secondColumn index)
        (firstDiagonal * secondDiagonal) := by
  apply Blocks.ext
  · rw [Rectangular.mul_at, sumFin_succ, lower_zero_zero, lower_zero_zero, lower_zero_zero]
    have zeroTail : sumFin (fun index : Fin dimension =>
        lower firstCorner firstColumn firstDiagonal 0 index.succ *
          lower secondCorner secondColumn secondDiagonal index.succ 0) = 0 := by
      rw [sumFin_congr (right := fun _ => (0 : K)) (fun index => by
        rw [lower_zero_succ]
        exact zero_mul _), sumFin_zero]
    rw [zeroTail, add_zero]
  · intro last
    rw [Rectangular.mul_at, sumFin_succ, lower_zero_zero, lower_zero_succ, lower_zero_succ]
    have zeroTail : sumFin (fun index : Fin dimension =>
        lower firstCorner firstColumn firstDiagonal 0 index.succ *
          lower secondCorner secondColumn secondDiagonal index.succ last.succ) = 0 := by
      rw [sumFin_congr (right := fun _ => (0 : K)) (fun index => by
        rw [lower_zero_succ]
        exact zero_mul _), sumFin_zero]
    rw [zeroTail]
    ring0
  · intro row
    rw [Rectangular.mul_at, sumFin_succ, lower_succ_zero, lower_zero_zero,
      lower_succ_zero, vectorOfFn_apply]
    have columnProduct : sumFin (fun index : Fin dimension =>
        lower firstCorner firstColumn firstDiagonal row.succ index.succ *
          lower secondCorner secondColumn secondDiagonal index.succ 0) =
        firstDiagonal * secondColumn row := by
      rw [sumFin_congr (right := fun index =>
        Multiplication.scaleIdentity firstDiagonal row index * secondColumn index)
        (fun index => by rw [lower_succ_succ, lower_succ_zero])]
      rw [← Multiplication.matrixVector_apply, Multiplication.matrixVector_scaleIdentity, vectorOfFn_apply]
    rw [columnProduct]
  · intro row last
    rw [Rectangular.mul_at, sumFin_succ, lower_succ_zero, lower_zero_succ,
      lower_succ_succ]
    have tailProduct : sumFin (fun index : Fin dimension =>
        lower firstCorner firstColumn firstDiagonal row.succ index.succ *
          lower secondCorner secondColumn secondDiagonal index.succ last.succ) =
        Multiplication.scaleIdentity firstDiagonal row last * secondDiagonal := by
      rw [sumFin_congr (right := fun index =>
        Multiplication.scaleIdentity firstDiagonal row index *
          Multiplication.scaleIdentity secondDiagonal index last)
        (fun index => by rw [lower_succ_succ, lower_succ_succ])]
      rw [← Rectangular.mul_at, Rectangular.mul_scaleIdentity, Rectangular.ofFn_apply]
    rw [tailProduct, Multiplication.scaleIdentity_apply, Multiplication.scaleIdentity_apply]
    by_cases equal : row = last
    · rw [if_pos equal, if_pos equal]
      ring0
    · rw [if_neg equal, if_neg equal]
      ring0

/-- The leading row of a lower triangular product scales the same original row. -/
theorem lower_mul_zero {columns : Nat} (corner diagonal : K) (column : Vec K dimension)
    (matrix : Rectangular K (dimension + 1) columns) (last : Fin columns) :
    Rectangular.mul (lower corner column diagonal) matrix 0 last = corner * matrix 0 last := by
  rw [Rectangular.mul_at, sumFin_succ, lower_zero_zero]
  have zeroTail : sumFin (fun index : Fin dimension =>
      lower corner column diagonal 0 index.succ * matrix index.succ last) = 0 := by
    rw [sumFin_congr (right := fun _ => (0 : K)) (fun index => by
      rw [lower_zero_succ]
      exact zero_mul _), sumFin_zero]
  rw [zeroTail, add_zero]

/-- A remaining lower triangular product row uses its original column correction and row. -/
theorem lower_mul_succ {columns : Nat} (corner diagonal : K) (column : Vec K dimension)
    (matrix : Rectangular K (dimension + 1) columns) (row : Fin dimension) (last : Fin columns) :
    Rectangular.mul (lower corner column diagonal) matrix row.succ last =
      column row * matrix 0 last + diagonal * matrix row.succ last := by
  rw [Rectangular.mul_at, sumFin_succ, lower_succ_zero]
  have tailProduct : sumFin (fun index : Fin dimension =>
      lower corner column diagonal row.succ index.succ * matrix index.succ last) =
      diagonal * matrix row.succ last := by
    let values := vectorOfFn fun index : Fin dimension => matrix index.succ last
    calc
      _ = sumFin (fun index : Fin dimension =>
          Multiplication.scaleIdentity diagonal row index * values index) :=
        sumFin_congr (fun index => by
          rw [lower_succ_succ]
          dsimp only [values]
          rw [vectorOfFn_apply])
      _ = Multiplication.matrixVector (Multiplication.scaleIdentity diagonal) values row :=
        (Multiplication.matrixVector_apply _ _ _).symm
      _ = diagonal * values row := by
        rw [Multiplication.matrixVector_scaleIdentity, vectorOfFn_apply]
      _ = _ := congrArg (fun value => diagonal * value) (vectorOfFn_apply _ _)
  rw [tailProduct]

/-- The leading column of a product with a transposed lower border scales the original column. -/
theorem mul_transpose_lower_zero {rows : Nat} (corner diagonal : K) (column : Vec K dimension)
    (matrix : Rectangular K rows (dimension + 1)) (row : Fin rows) :
    Rectangular.mul matrix (Rectangular.transpose (lower corner column diagonal)) row 0 =
      corner * matrix row 0 := by
  have agreement : Rectangular.mul matrix (Rectangular.transpose (lower corner column diagonal)) =
      Rectangular.transpose (Rectangular.mul (lower corner column diagonal) (Rectangular.transpose matrix)) := by
    rw [Rectangular.transpose_mul, Rectangular.transpose_transpose]
  rw [agreement, Rectangular.transpose_apply, lower_mul_zero, Rectangular.transpose_apply]

/-- A remaining transposed lower product column uses its original row correction and column. -/
theorem mul_transpose_lower_succ {rows : Nat} (corner diagonal : K) (column : Vec K dimension)
    (matrix : Rectangular K rows (dimension + 1)) (row : Fin rows) (last : Fin dimension) :
    Rectangular.mul matrix (Rectangular.transpose (lower corner column diagonal)) row last.succ =
      column last * matrix row 0 + diagonal * matrix row last.succ := by
  have agreement : Rectangular.mul matrix (Rectangular.transpose (lower corner column diagonal)) =
      Rectangular.transpose (Rectangular.mul (lower corner column diagonal) (Rectangular.transpose matrix)) := by
    rw [Rectangular.transpose_mul, Rectangular.transpose_transpose]
  rw [agreement, Rectangular.transpose_apply, lower_mul_succ,
    Rectangular.transpose_apply, Rectangular.transpose_apply]

/-- Construct the retained actual inverse of a lower triangular border from its two scalar units.

The cached inverse column is computed once from the original column and the two
specific supplied inverses. Both products use the original structural matrix
multiplication and have scalar one.
-/
@[expose] def lowerInverse (corner diagonal : K) (column : Vec K dimension)
    (cornerInverse : K) (cornerUnit : corner * cornerInverse = 1)
    (diagonalInverse : K) (diagonalUnit : diagonal * diagonalInverse = 1) :
    ScaledInverse (lower corner column diagonal) where
  scalar := 1
  inverse := lower cornerInverse
    (vectorOfFn fun index => -diagonalInverse * column index * cornerInverse) diagonalInverse
  left_identity := by
    change Rectangular.mul _ _ = _
    rw [lower_mul]
    have columnZero :
        (vectorOfFn fun index =>
          (vectorOfFn (fun inner => -diagonalInverse * column inner * cornerInverse)) index * corner +
            diagonalInverse * column index) = vectorOfFn (fun _ : Fin dimension => (0 : K)) := by
      apply vector_ext
      intro index
      rw [vectorOfFn_apply, vectorOfFn_apply, vectorOfFn_apply]
      calc
        _ = diagonalInverse * column index * (1 - corner * cornerInverse) := by ring0
        _ = 0 := by rw [cornerUnit]; ring0
    rw [columnZero, mul_comm cornerInverse corner, cornerUnit,
      mul_comm diagonalInverse diagonal, diagonalUnit]
    exact lower_unit
  right_identity := by
    change Rectangular.mul _ _ = _
    rw [lower_mul]
    have columnZero :
        (vectorOfFn fun index => column index * cornerInverse + diagonal *
          (vectorOfFn (fun inner => -diagonalInverse * column inner * cornerInverse)) index) =
          vectorOfFn (fun _ : Fin dimension => (0 : K)) := by
      apply vector_ext
      intro index
      rw [vectorOfFn_apply, vectorOfFn_apply, vectorOfFn_apply]
      calc
        _ = column index * cornerInverse * (1 - diagonal * diagonalInverse) := by ring0
        _ = 0 := by rw [diagonalUnit]; ring0
    rw [columnZero, cornerUnit, diagonalUnit]
    exact lower_unit

end Purelib.LinearAlgebra.Matrix.Triangular

end
