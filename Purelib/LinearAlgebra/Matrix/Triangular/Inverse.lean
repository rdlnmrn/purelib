module

public import Purelib.LinearAlgebra.Matrix.Triangular
import Purelib.Data.Fin
import Purelib.Tactic.Ring

/-!
# Triangular inverse construction from retained diagonal units

The original square matrix and its diagonal inverse table determine the
complete inverse by structural dimension recursion. Each step retains its
actual tail and the existing triangular border; no field division is used.
-/

public section

namespace Purelib.LinearAlgebra.Matrix.Triangular

open Purelib
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.LinearAlgebra.Matrix
open Inverse.Scaled.Basic

variable {K : Type*} [CommRing K]

/-- All entries strictly below the original matrix diagonal are zero. -/
@[expose] def IsUpper {dimension : Nat} (matrix : SquareMatrix K dimension) : Prop :=
  ∀ row column, column.val < row.val → matrix row column = 0

/-- Deleting the leading row and column preserves the original upper-triangular property. -/
theorem upper_tail {dimension : Nat} {matrix : SquareMatrix K (dimension + 1)}
    (upper : IsUpper matrix) : IsUpper (Blocks.tail matrix) := by
  intro row column before
  rw [Blocks.tail_apply]
  exact upper row.succ column.succ (Nat.succ_lt_succ before)

/-- A matrix with zero lower leading column factors through its original tail and triangular border. -/
theorem border_factorization {dimension : Nat} (matrix : SquareMatrix K (dimension + 1))
    (columnZero : ∀ row : Fin dimension, matrix row.succ 0 = 0) :
    matrix = Rectangular.mul (Blocks.diagonal 1 (Blocks.tail matrix))
      (Rectangular.transpose (lower (Blocks.head matrix) (Blocks.topRow matrix) 1)) := by
  apply Blocks.ext
  · rw [mul_transpose_lower_zero, Blocks.diagonal_zero_zero, mul_one]
    rfl
  · intro column
    rw [mul_transpose_lower_succ, Blocks.diagonal_zero_zero,
      Blocks.diagonal_zero_succ, mul_one, mul_zero, add_zero, Blocks.topRow_apply]
  · intro row
    rw [mul_transpose_lower_zero, Blocks.diagonal_succ_zero, mul_zero]
    exact columnZero row
  · intro row column
    rw [mul_transpose_lower_succ, Blocks.diagonal_succ_zero,
      Blocks.diagonal_succ_succ, mul_zero, zero_add, one_mul, Blocks.tail_apply]

/-- A retained unit leading row and zero lower column factor through the same original tail.

The supplied tail remains unchanged in the diagonal factor. No new tail
matrix is materialized to certify this decomposition.
-/
theorem unit_border_factorization {dimension : Nat} (top : Vec K dimension)
    (remaining : SquareMatrix K dimension) :
    Blocks.border 1 top (vectorOfFn fun _ => 0) remaining =
      Rectangular.mul (Blocks.diagonal 1 remaining) (Rectangular.transpose (lower 1 top 1)) := by
  apply Blocks.ext
  · rw [Blocks.border_zero_zero, mul_transpose_lower_zero, Blocks.diagonal_zero_zero, mul_one]
  · intro column
    rw [Blocks.border_zero_succ, mul_transpose_lower_succ, Blocks.diagonal_zero_zero,
      Blocks.diagonal_zero_succ, mul_one, mul_zero, add_zero]
  · intro row
    rw [Blocks.border_succ_zero, vectorOfFn_apply, mul_transpose_lower_zero,
      Blocks.diagonal_succ_zero, mul_zero]
  · intro row column
    rw [Blocks.border_succ_succ, mul_transpose_lower_succ, Blocks.diagonal_succ_zero,
      Blocks.diagonal_succ_succ, mul_zero, zero_add, one_mul]

/-- Invert a unit leading border using the same retained tail inverse.

The original diagonal extension and transposed scalar-tail inverse supply
both identities. The resulting record refers to the exact supplied border.
-/
@[expose] def inverseUnitBorder {dimension : Nat} (top : Vec K dimension)
    {remaining : SquareMatrix K dimension} (remainingInverse : ScaledInverse remaining)
    (unit : remainingInverse.scalar = 1) :
    ScaledInverse (Blocks.border 1 top (vectorOfFn fun _ => 0) remaining) := by
  let diagonal := remainingInverse.diagonal unit
  let border := (lowerInverse 1 1 top 1 (one_mul 1) 1 (one_mul 1)).transpose
  let combined := diagonal.mul (by rfl) border (by rfl)
  have factorization := unit_border_factorization top remaining
  exact
    { scalar := 1
      inverse := combined.inverse
      left_identity :=
        (congrArg (fun candidate => Multiplication.mul combined.inverse candidate) factorization).trans
          combined.left_identity
      right_identity :=
        (congrArg (fun candidate => Multiplication.mul candidate combined.inverse) factorization).trans
          combined.right_identity }

/-- The retained unit-border inverse has common scalar one. -/
theorem inverseUnitBorder_scalar {dimension : Nat} (top : Vec K dimension)
    {remaining : SquareMatrix K dimension} (remainingInverse : ScaledInverse remaining)
    (unit : remainingInverse.scalar = 1) : (inverseUnitBorder top remainingInverse unit).scalar = 1 := rfl

/-- An upper matrix is the product of its original diagonal tail and transposed lower border. -/
theorem upper_factorization {dimension : Nat} (matrix : SquareMatrix K (dimension + 1))
    (upper : IsUpper matrix) :
    matrix = Rectangular.mul (Blocks.diagonal 1 (Blocks.tail matrix))
      (Rectangular.transpose (lower (Blocks.head matrix) (Blocks.topRow matrix) 1)) :=
  border_factorization matrix (fun row => upper row.succ 0 (Nat.zero_lt_succ row.val))

/-- Construct the complete original upper-triangular inverse using the same retained diagonal units.

Each recursive call uses the actual smaller original tail. The diagonal
extension and the transposed border retain their existing inverse records,
and their composed cached inverse is certified against the original input.
-/
@[expose] def inverseUpper : {dimension : Nat} → (matrix : SquareMatrix K dimension) →
    IsUpper matrix → (diagonalInverses : Vec K dimension) →
    (∀ index, matrix index index * diagonalInverses index = 1) →
    { inverse : ScaledInverse matrix // inverse.scalar = 1 }
  | 0, matrix, _, _, _ =>
      ⟨{ scalar := 1
         inverse := .nil
         left_identity := by
          apply matrix_ext
          intro row
          exact Fin.elim0 row
         right_identity := by
          apply matrix_ext
          intro row
          exact Fin.elim0 row }, rfl⟩
  | dimension + 1, matrix, upper, diagonalInverses, units => by
      let remaining := Blocks.tail matrix
      let remainingInverses := vectorOfFn fun index : Fin dimension => diagonalInverses index.succ
      let smaller := inverseUpper remaining (upper_tail upper) remainingInverses (by
        intro index
        dsimp only [remaining, remainingInverses]
        rw [Blocks.tail_apply, vectorOfFn_apply]
        exact units index.succ)
      let diagonal := smaller.val.diagonal smaller.property
      let border := (lowerInverse (Blocks.head matrix) 1 (Blocks.topRow matrix)
        (diagonalInverses 0) (units 0) 1 (one_mul 1)).transpose
      let combined := diagonal.mul (by rfl) border (by rfl)
      have factorization := upper_factorization matrix upper
      exact
        ⟨{ scalar := 1
           inverse := combined.inverse
           left_identity := by
            exact (congrArg (fun candidate => Multiplication.mul combined.inverse candidate)
              factorization).trans combined.left_identity
           right_identity := by
            exact (congrArg (fun candidate => Multiplication.mul candidate combined.inverse)
              factorization).trans combined.right_identity }, rfl⟩

/-- The same triangular inverse construction always retains scalar one. -/
theorem inverseUpper_scalar {dimension : Nat} (matrix : SquareMatrix K dimension)
    (upper : IsUpper matrix) (diagonalInverses : Vec K dimension)
    (units : ∀ index, matrix index index * diagonalInverses index = 1) :
    (inverseUpper matrix upper diagonalInverses units).val.scalar = 1 :=
  (inverseUpper matrix upper diagonalInverses units).property

/-- All entries strictly above the original matrix diagonal are zero. -/
@[expose] def IsLower {dimension : Nat} (matrix : SquareMatrix K dimension) : Prop :=
  ∀ row column, row.val < column.val → matrix row column = 0

/-- Transposing a lower matrix gives an upper matrix with its original entries. -/
theorem lower_transpose {dimension : Nat} {matrix : SquareMatrix K dimension}
    (lower : IsLower matrix) : IsUpper (Rectangular.transpose matrix) := by
  intro row column before
  rw [Rectangular.transpose_apply]
  exact lower column row before

/-- Construct the complete lower-triangular inverse from the same original diagonal units.

The upper constructor consumes the original transpose once. Transposing its
retained inverse recovers the original matrix's inverse and scalar-one proof.
-/
@[expose] def inverseLower {dimension : Nat} (matrix : SquareMatrix K dimension)
    (lower : IsLower matrix) (diagonalInverses : Vec K dimension)
    (units : ∀ index, matrix index index * diagonalInverses index = 1) :
    { inverse : ScaledInverse matrix // inverse.scalar = 1 } := by
  let upper := inverseUpper (Rectangular.transpose matrix) (lower_transpose lower) diagonalInverses (by
    intro index
    rw [Rectangular.transpose_apply]
    exact units index)
  let transposed := upper.val.transpose
  have target := Rectangular.transpose_transpose matrix
  have left : Multiplication.mul transposed.inverse matrix = Multiplication.scaleIdentity 1 :=
    (congrArg (fun candidate => Multiplication.mul transposed.inverse candidate) target.symm).trans
      (transposed.left_identity.trans (congrArg Multiplication.scaleIdentity upper.property))
  have right : Multiplication.mul matrix transposed.inverse = Multiplication.scaleIdentity 1 :=
    (congrArg (fun candidate => Multiplication.mul candidate transposed.inverse) target.symm).trans
      (transposed.right_identity.trans (congrArg Multiplication.scaleIdentity upper.property))
  exact ⟨{ scalar := 1
           inverse := transposed.inverse
           left_identity := left
           right_identity := right }, rfl⟩

/-- The lower constructor retains the same scalar-one guarantee as the upper constructor. -/
theorem inverseLower_scalar {dimension : Nat} (matrix : SquareMatrix K dimension)
    (lower : IsLower matrix) (diagonalInverses : Vec K dimension)
    (units : ∀ index, matrix index index * diagonalInverses index = 1) :
    (inverseLower matrix lower diagonalInverses units).val.scalar = 1 :=
  (inverseLower matrix lower diagonalInverses units).property

end Purelib.LinearAlgebra.Matrix.Triangular
