module

public import Purelib.LinearAlgebra.Matrix.NormalForm.Basic
public import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Construction
public import Purelib.LinearAlgebra.Matrix.Schur.Reduction
public import Purelib.LinearAlgebra.Matrix.Permutation
import Purelib.Tactic.QuotientFreeOmega

/-!
# Certified rectangular coordinate reduction

The constructors retain the original matrix, actual coordinate products and
both original inverse identities. Unit-pivot reduction proceeds through the
same original fraction-free Schur rectangle.
-/

public section

namespace Purelib.LinearAlgebra.Matrix.NormalForm

open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.LinearAlgebra.Matrix
open Inverse.Scaled.Basic

variable {K : Type*} [CommRing K] {rows columns : Nat}

/-- Transport a retained normal form along equality of its original rectangle. -/
@[expose] def ofEq {matrix other : Rectangular K rows columns}
    (equal : matrix = other) (normal : NormalForm matrix) : NormalForm other :=
  equal ▸ normal

/-- Transporting the same original rectangle preserves its retained identity-block size. -/
theorem ofEq_rank {matrix other : Rectangular K rows columns}
    (equal : matrix = other) (normal : NormalForm matrix) : (ofEq equal normal).rank = normal.rank := by
  cases equal
  rfl

/-- An all-zero original rectangle is reduced by the two unchanged identity coordinates. -/
@[expose] def ofZero (matrix : Rectangular K rows columns)
    (zero : ∀ row column, matrix row column = 0) : NormalForm matrix where
  rank := 0
  rank_le_rows := Nat.zero_le _
  rank_le_columns := Nat.zero_le _
  source := Multiplication.scaleIdentity 1
  sourceInverse := ScaledInverse.identity columns
  source_scalar := rfl
  target := Multiplication.scaleIdentity 1
  targetInverse := ScaledInverse.identity rows
  target_scalar := rfl
  reduced := matrix
  reduced_eq := by rw [Rectangular.unit_mul, Rectangular.mul_unit]
  reduced_apply := fun row column => by
    rw [zero row column, if_neg (fun condition => Nat.not_lt_zero _ condition.2)]

/-- Pull a retained reduction back through two actual invertible coordinate changes.

The transformed rectangle and its complete product identity are supplied with
both original inverse records. The resulting coordinates compose their same
cached matrices and retain the same reduced rectangle and block size.
-/
@[expose] def pullback {matrix transformed : Rectangular K rows columns}
    (left : SquareMatrix K rows) (leftInverse : ScaledInverse left)
    (leftUnit : leftInverse.scalar = 1)
    (right : SquareMatrix K columns) (rightInverse : ScaledInverse right)
    (rightUnit : rightInverse.scalar = 1)
    (transformed_eq : transformed = Rectangular.mul (Rectangular.mul left matrix) right)
    (normal : NormalForm transformed) : NormalForm matrix where
  rank := normal.rank
  rank_le_rows := normal.rank_le_rows
  rank_le_columns := normal.rank_le_columns
  source := Multiplication.mul right normal.source
  sourceInverse := ScaledInverse.mul rightInverse rightUnit normal.sourceInverse normal.source_scalar
  source_scalar := rfl
  target := Multiplication.mul normal.target left
  targetInverse := ScaledInverse.mul normal.targetInverse normal.target_scalar leftInverse leftUnit
  target_scalar := rfl
  reduced := normal.reduced
  reduced_eq := by
    change normal.reduced = Rectangular.mul
      (Rectangular.mul (Rectangular.mul normal.target left) matrix)
      (Rectangular.mul right normal.source)
    calc
      normal.reduced = Rectangular.mul (Rectangular.mul normal.target transformed) normal.source :=
        normal.reduced_eq
      _ = Rectangular.mul (Rectangular.mul normal.target
          (Rectangular.mul (Rectangular.mul left matrix) right)) normal.source :=
        congrArg (fun value => Rectangular.mul (Rectangular.mul normal.target value) normal.source)
          transformed_eq
      _ = Rectangular.mul
          (Rectangular.mul (Rectangular.mul normal.target (Rectangular.mul left matrix)) right)
          normal.source := congrArg (fun value => Rectangular.mul value normal.source)
            (Rectangular.mul_assoc normal.target (Rectangular.mul left matrix) right).symm
      _ = Rectangular.mul (Rectangular.mul normal.target (Rectangular.mul left matrix))
          (Rectangular.mul right normal.source) := Rectangular.mul_assoc _ _ _
      _ = _ := congrArg (fun value => Rectangular.mul value (Rectangular.mul right normal.source))
        (Rectangular.mul_assoc normal.target left matrix).symm
  reduced_apply := normal.reduced_apply

/-- Extend a retained diagonal reduction by one leading identity coordinate. -/
@[expose] def ofDiagonal {matrix : Rectangular K rows columns} (normal : NormalForm matrix) :
    NormalForm (Blocks.diagonal 1 matrix) where
  rank := normal.rank + 1
  rank_le_rows := Nat.succ_le_succ normal.rank_le_rows
  rank_le_columns := Nat.succ_le_succ normal.rank_le_columns
  source := Blocks.diagonal 1 normal.source
  sourceInverse := ScaledInverse.diagonal normal.sourceInverse normal.source_scalar
  source_scalar := rfl
  target := Blocks.diagonal 1 normal.target
  targetInverse := ScaledInverse.diagonal normal.targetInverse normal.target_scalar
  target_scalar := rfl
  reduced := Blocks.diagonal 1 normal.reduced
  reduced_eq := by
    rw [Blocks.diagonal_mul, one_mul, Blocks.diagonal_mul, one_mul, normal.reduced_eq]
  reduced_apply := by
    intro row column
    refine Purelib.Data.Fin.cases_induction ?_ (fun row => ?_) row
    · refine Purelib.Data.Fin.cases_induction ?_ (fun column => ?_) column
      · change Blocks.diagonal 1 normal.reduced 0 0 = _
        rw [Blocks.diagonal_zero_zero, if_pos ⟨rfl, Nat.zero_lt_succ _⟩]
      · change Blocks.diagonal 1 normal.reduced 0 column.succ = _
        rw [Blocks.diagonal_zero_succ, if_neg (fun condition => Nat.noConfusion condition.1)]
    · refine Purelib.Data.Fin.cases_induction ?_ (fun column => ?_) column
      · change Blocks.diagonal 1 normal.reduced row.succ 0 = _
        rw [Blocks.diagonal_succ_zero, if_neg (fun condition => Nat.noConfusion condition.1)]
      · rw [Blocks.diagonal_succ_succ, normal.reduced_apply]
        by_cases condition : row.val = column.val ∧ row.val < normal.rank
        · rw [if_pos condition, if_pos ⟨congrArg Nat.succ condition.1, Nat.succ_lt_succ condition.2⟩]
        · rw [if_neg condition, if_neg (fun shifted =>
            condition ⟨Nat.succ.inj shifted.1, Nat.lt_of_succ_lt_succ shifted.2⟩)]

/-- Complete one cached original unit-pivot reduction using its same residual normal form. -/
@[expose] def ofUnitReduction {matrix : Rectangular K (rows + 1) (columns + 1)}
    (step : Schur.UnitReduction matrix) (normal : NormalForm step.residual) : NormalForm matrix :=
  pullback step.target step.targetInverse step.target_scalar
    step.source step.sourceInverse step.source_scalar step.reduction (ofDiagonal normal)

/-- Transport a normal form through the original two displayed row and column transpositions.

Both transposition matrices are computed once through their original inverse
records and reused as the actual coordinate matrices in the pullback.
-/
@[expose] def ofPivot {matrix : Rectangular K (rows + 1) (columns + 1)}
    (rowPivot : Fin (rows + 1)) (columnPivot : Fin (columns + 1))
    (normal : NormalForm (Permutation.pivotMatrix matrix rowPivot columnPivot)) : NormalForm matrix :=
  let rowInverse := Permutation.inverse (K := K) rowPivot
  let columnInverse := Permutation.inverse (K := K) columnPivot
  pullback rowInverse.inverse rowInverse rfl columnInverse.inverse columnInverse rfl
    (Permutation.pivotMatrix_eq_mul matrix rowPivot columnPivot) normal

end Purelib.LinearAlgebra.Matrix.NormalForm

end
