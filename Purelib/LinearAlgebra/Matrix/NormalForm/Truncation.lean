module

public import Purelib.LinearAlgebra.Matrix.NormalForm.Reduction
public import Purelib.LinearAlgebra.Matrix.Rectangular.Identity

/-!
# Initial rectangles of retained invertible matrices

The same original square inverse normalizes either an initial row rectangle
or an initial column rectangle. Both constructors retain the actual truncated
identity, coordinate matrices and original scalar-one inverse certificates.
-/

public section

namespace Purelib.LinearAlgebra.Matrix.NormalForm

open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.LinearAlgebra.Matrix
open Inverse.Scaled.Basic

variable {K : Type*} [CommRing K] {size cut : Nat} {matrix : SquareMatrix K size}

/-- Transport the same retained normal form along equality of its original two dimensions. -/
@[expose] def cast {otherRows otherColumns : Nat} {matrix : Rectangular K size cut}
    (rowSize : size = otherRows) (columnSize : cut = otherColumns) (normal : NormalForm matrix) :
    NormalForm (Rectangular.cast rowSize columnSize matrix) := by
  cases rowSize
  cases columnSize
  exact normal

/-- Transporting dimensions preserves the same actual identity-block size. -/
theorem cast_rank {otherRows otherColumns : Nat} {matrix : Rectangular K size cut}
    (rowSize : size = otherRows) (columnSize : cut = otherColumns) (normal : NormalForm matrix) :
    (cast rowSize columnSize normal).rank = normal.rank := by
  cases rowSize
  cases columnSize
  rfl

/-- Normalize the original initial rows using the same retained square inverse on the right. -/
@[expose] def ofInitialRows (bound : cut ≤ size) (inverse : ScaledInverse matrix)
    (unit : inverse.scalar = 1) : NormalForm (Rectangular.takeRows bound matrix) where
  rank := cut
  rank_le_rows := Nat.le_refl _
  rank_le_columns := bound
  source := inverse.inverse
  sourceInverse := inverse.symm unit
  source_scalar := rfl
  target := Multiplication.scaleIdentity 1
  targetInverse := ScaledInverse.identity cut
  target_scalar := rfl
  reduced := Rectangular.takeRows bound (Multiplication.scaleIdentity 1)
  reduced_eq := by
    rw [Rectangular.unit_mul, ← Rectangular.takeRows_mul]
    exact congrArg (Rectangular.takeRows bound)
      (inverse.right_identity.trans (congrArg Multiplication.scaleIdentity unit)).symm
  reduced_apply := by
    intro row column
    rw [Rectangular.takeRows_at, Multiplication.scaleIdentity_apply]
    by_cases same : row.val = column.val
    · rw [if_pos (Fin.ext same), if_pos ⟨same, row.isLt⟩]
    · rw [if_neg (fun equal => same (congrArg Fin.val equal)), if_neg (fun condition => same condition.1)]

/-- Normalize the original initial columns using the same retained square inverse on the left. -/
@[expose] def ofInitialColumns (bound : cut ≤ size) (inverse : ScaledInverse matrix)
    (unit : inverse.scalar = 1) : NormalForm (Rectangular.takeColumns bound matrix) where
  rank := cut
  rank_le_rows := bound
  rank_le_columns := Nat.le_refl _
  source := Multiplication.scaleIdentity 1
  sourceInverse := ScaledInverse.identity cut
  source_scalar := rfl
  target := inverse.inverse
  targetInverse := inverse.symm unit
  target_scalar := rfl
  reduced := Rectangular.takeColumns bound (Multiplication.scaleIdentity 1)
  reduced_eq := by
    rw [Rectangular.mul_unit, ← Rectangular.takeColumns_mul]
    exact congrArg (Rectangular.takeColumns bound)
      (inverse.left_identity.trans (congrArg Multiplication.scaleIdentity unit)).symm
  reduced_apply := by
    intro row column
    rw [Rectangular.takeColumns_at, Multiplication.scaleIdentity_apply]
    by_cases same : row.val = column.val
    · have inside : row.val < cut := same ▸ column.isLt
      rw [if_pos (Fin.ext same), if_pos ⟨same, inside⟩]
    · rw [if_neg (fun equal => same (congrArg Fin.val equal)), if_neg (fun condition => same condition.1)]

/-- The initial-row constructor retains exactly its actual row count as the identity-block size. -/
theorem ofInitialRows_rank (bound : cut ≤ size) (inverse : ScaledInverse matrix) (unit : inverse.scalar = 1) :
    (ofInitialRows bound inverse unit).rank = cut := rfl

/-- The initial-column constructor retains exactly its actual column count as the identity-block size. -/
theorem ofInitialColumns_rank (bound : cut ≤ size) (inverse : ScaledInverse matrix) (unit : inverse.scalar = 1) :
    (ofInitialColumns bound inverse unit).rank = cut := rfl

end Purelib.LinearAlgebra.Matrix.NormalForm

end
