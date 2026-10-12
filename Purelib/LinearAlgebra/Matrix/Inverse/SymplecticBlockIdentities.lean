module
import Purelib.Data.Nat.Addition
import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Multiplication

import Purelib.Data.Fin
public import Purelib.LinearAlgebra.Matrix.Blocks
import Purelib.LinearAlgebra.Matrix.Inverse.SquareInverseCancellation
import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

section

open Purelib.Algebra

open Purelib

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

public section

/-! Column symplectic identities imply row identities by the finite square inverse. -/
namespace Purelib.LinearAlgebra.Matrix.Inverse.SymplecticBlockIdentities

open Purelib.LinearAlgebra
/-- The exact Gaussian rational coefficient type. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical
attribute [local congr] FiniteSum.Fin.sumFin_congr

variable {n : Nat} (p q r s : SquareMatrix
  Purelib.LinearAlgebra.Matrix.Inverse.SymplecticBlockIdentities.Gaussian n)

/-- Assemble the transposed symplectic inverse candidate from the four retained blocks.

The diagonal blocks are the transposes of the opposite diagonal blocks, and the off-diagonal blocks are negated
transposes. -/
@[expose] def inverseBlock : SquareMatrix SquareMatrix.Inverse.SymplecticBlockIdentities.Gaussian (n + n) :=
  SquareMatrix.Blocks.block (SquareMatrix.matrixOfFn fun row column => s column row)
    (SquareMatrix.matrixOfFn fun row column => -q column row)
    (SquareMatrix.matrixOfFn fun row column => -r column row) (SquareMatrix.matrixOfFn fun row column => p
      column row)

/-- The equality indicator for first-block indices equals the original coordinate indicator with reversed arguments. -/
private theorem left_delta (row column : Fin n) :
    (if Fin.castAdd n row = Fin.castAdd n column then (1 : SquareMatrix.Inverse.SymplecticBlockIdentities.Gaussian) else
      0) = if column = row then 1 else 0 := by
  by_cases same : column = row
  · rw [if_pos same, if_pos (congrArg (Fin.castAdd n) same.symm)]
  · have apart : Fin.castAdd n row ≠ Fin.castAdd n column := by
      intro equal
      exact same (Fin.ext (congrArg (fun index : Fin (n + n) => index.val) equal).symm)
    rw [if_neg same, if_neg apart]

/-- The equality indicator for second-block indices equals the original coordinate indicator. -/
private theorem right_delta (row column : Fin n) :
    (if Fin.natAdd n row = Fin.natAdd n column then (1 : SquareMatrix.Inverse.SymplecticBlockIdentities.Gaussian) else
      0) = if row = column then 1 else 0 := by
  by_cases same : row = column
  · rw [if_pos same, if_pos (congrArg (Fin.natAdd n) same)]
  · rw [if_neg same, if_neg (fun equal => same (Fin.ext (Data.Nat.Addition.add_left_cancel (congrArg Fin.val equal))))]

/-- A coordinate in the first finite block differs from every coordinate in the second block. -/
private theorem separate (row column : Fin n) : Fin.castAdd n row ≠ Fin.natAdd n column := by
  intro equal
  have same := congrArg Fin.val equal
  change row.val = n + column.val at same
  have below := row.isLt
  omega

variable
  (pp : ∀ row column, FiniteSum.Fin.sumFin (fun index => p index row * r index column - r index row * p index column) =
    0)
  (qq : ∀ row column, FiniteSum.Fin.sumFin (fun index => q index row * s index column - s index row * q index column) =
    0)
  (pq : ∀ row column, FiniteSum.Fin.sumFin (fun index => p index row * s index column - r index row * q index column) =
    if row = column then 1 else 0)

include pp qq pq

/-- The retained symplectic column identities make the candidate a left inverse of the block matrix. -/
theorem inverseBlock_mul : SquareMatrix.Multiplication.mul (SquareMatrix.Inverse.SymplecticBlockIdentities.inverseBlock
  p q r s) (SquareMatrix.Blocks.block p q r s) = SquareMatrix.Multiplication.scaleIdentity 1 := by
  apply SquareMatrix.matrix_ext
  intro row column
  rcases Data.Fin.addCases_split row with ⟨row, rfl⟩ | ⟨row, rfl⟩ <;>
    rcases Data.Fin.addCases_split column with ⟨column, rfl⟩ | ⟨column, rfl⟩
  · rw [SquareMatrix.Multiplication.mul_apply, FiniteSum.Fin.sumFin_split,
      SquareMatrix.Multiplication.scaleIdentity_apply,
      LinearAlgebra.Matrix.Inverse.SymplecticBlockIdentities.left_delta]
    simp only [SquareMatrix.Inverse.SymplecticBlockIdentities.inverseBlock, SquareMatrix.Blocks.block_ll,
      SquareMatrix.Blocks.block_lr, SquareMatrix.Blocks.block_rl, SquareMatrix.matrixOfFn_apply]
    rw [← FiniteSum.Fin.sumFin_add]
    exact (FiniteSum.Fin.sumFin_congr (fun index => by ring1)).trans (pq column row)
  · rw [SquareMatrix.Multiplication.mul_apply, FiniteSum.Fin.sumFin_split,
      SquareMatrix.Multiplication.scaleIdentity_apply, if_neg
      (LinearAlgebra.Matrix.Inverse.SymplecticBlockIdentities.separate row column)]
    simp only [SquareMatrix.Inverse.SymplecticBlockIdentities.inverseBlock, SquareMatrix.Blocks.block_ll,
      SquareMatrix.Blocks.block_lr, SquareMatrix.Blocks.block_rr, SquareMatrix.matrixOfFn_apply]
    rw [← FiniteSum.Fin.sumFin_add]
    exact (FiniteSum.Fin.sumFin_congr (fun index => by ring1)).trans (qq column row)
  · rw [SquareMatrix.Multiplication.mul_apply, FiniteSum.Fin.sumFin_split,
      SquareMatrix.Multiplication.scaleIdentity_apply, if_neg (Ne.symm
      (LinearAlgebra.Matrix.Inverse.SymplecticBlockIdentities.separate column row))]
    simp only [SquareMatrix.Inverse.SymplecticBlockIdentities.inverseBlock, SquareMatrix.Blocks.block_rl,
      SquareMatrix.Blocks.block_rr, SquareMatrix.Blocks.block_ll, SquareMatrix.matrixOfFn_apply]
    rw [← FiniteSum.Fin.sumFin_add]
    exact (FiniteSum.Fin.sumFin_congr (fun index => by ring1)).trans (pp row column)
  · rw [SquareMatrix.Multiplication.mul_apply, FiniteSum.Fin.sumFin_split,
      SquareMatrix.Multiplication.scaleIdentity_apply,
      LinearAlgebra.Matrix.Inverse.SymplecticBlockIdentities.right_delta]
    simp only [SquareMatrix.Inverse.SymplecticBlockIdentities.inverseBlock, SquareMatrix.Blocks.block_rl,
      SquareMatrix.Blocks.block_rr, SquareMatrix.Blocks.block_lr, SquareMatrix.matrixOfFn_apply]
    rw [← FiniteSum.Fin.sumFin_add]
    exact (FiniteSum.Fin.sumFin_congr (fun index => by ring1)).trans (pq row column)

/-- The retained symplectic column identities also make the candidate a right inverse. -/
theorem mul_inverseBlock : SquareMatrix.Multiplication.mul (SquareMatrix.Blocks.block p q r s)
  (SquareMatrix.Inverse.SymplecticBlockIdentities.inverseBlock p q r s) = SquareMatrix.Multiplication.scaleIdentity 1 :=
  SquareMatrix.Inverse.SquareInverseCancellation.reverse_inverse _ _
    (SquareMatrix.Inverse.SymplecticBlockIdentities.inverseBlock_mul p q r s pp qq pq)

/-- The first two block rows have zero signed wedge pairing under the supplied column identities. -/
theorem first_row_wedges (row column : Fin n) :
    FiniteSum.Fin.sumFin (fun index => p row index * q column index - q row index * p column index) = 0 := by
  have equal := SquareMatrix.matrix_eq_at (SquareMatrix.Inverse.SymplecticBlockIdentities.mul_inverseBlock p q r s
    pp qq pq) (Fin.castAdd n row) (Fin.natAdd n column)
  rw [SquareMatrix.Multiplication.mul_apply, FiniteSum.Fin.sumFin_split,
    SquareMatrix.Multiplication.scaleIdentity_apply, if_neg
    (LinearAlgebra.Matrix.Inverse.SymplecticBlockIdentities.separate row column)] at equal
  simp only [SquareMatrix.Inverse.SymplecticBlockIdentities.inverseBlock, SquareMatrix.Blocks.block_ll,
    SquareMatrix.Blocks.block_lr, SquareMatrix.Blocks.block_rr, SquareMatrix.matrixOfFn_apply] at equal
  rw [← FiniteSum.Fin.sumFin_add] at equal
  have negative : -FiniteSum.Fin.sumFin (fun index => p row index * q column index - q row index * p column index) = 0
    := by
    apply Eq.trans _ equal
    exact (FiniteSum.Fin.sumFin_neg _).symm.trans (FiniteSum.Fin.sumFin_congr (fun index => by ring1))
  exact (neg_neg _).symm.trans ((congrArg Neg.neg negative).trans neg_zero)

/-- The last two block rows have zero signed wedge pairing under the supplied column identities. -/
theorem last_row_wedges (row column : Fin n) :
    FiniteSum.Fin.sumFin (fun index => r row index * s column index - s row index * r column index) = 0 := by
  have equal := SquareMatrix.matrix_eq_at (SquareMatrix.Inverse.SymplecticBlockIdentities.mul_inverseBlock p q r s
    pp qq pq) (Fin.natAdd n row) (Fin.castAdd n column)
  rw [SquareMatrix.Multiplication.mul_apply, FiniteSum.Fin.sumFin_split,
    SquareMatrix.Multiplication.scaleIdentity_apply, if_neg (Ne.symm
    (LinearAlgebra.Matrix.Inverse.SymplecticBlockIdentities.separate column row))] at equal
  simp only [SquareMatrix.Inverse.SymplecticBlockIdentities.inverseBlock, SquareMatrix.Blocks.block_rl,
    SquareMatrix.Blocks.block_rr, SquareMatrix.Blocks.block_ll, SquareMatrix.matrixOfFn_apply] at equal
  rw [← FiniteSum.Fin.sumFin_add] at equal
  exact (FiniteSum.Fin.sumFin_congr (fun index => by ring1)).trans equal

/-- The mixed block-row pairing is the coordinate identity under the supplied column identities. -/
theorem mixed_row_wedges (row column : Fin n) :
    FiniteSum.Fin.sumFin (fun index => p row index * s column index - q row index * r column index) =
      if row = column then 1 else 0 := by
  have equal := SquareMatrix.matrix_eq_at (SquareMatrix.Inverse.SymplecticBlockIdentities.mul_inverseBlock p q r s
    pp qq pq) (Fin.castAdd n row) (Fin.castAdd n column)
  rw [SquareMatrix.Multiplication.mul_apply, FiniteSum.Fin.sumFin_split,
    SquareMatrix.Multiplication.scaleIdentity_apply,
    LinearAlgebra.Matrix.Inverse.SymplecticBlockIdentities.left_delta] at equal
  simp only [SquareMatrix.Inverse.SymplecticBlockIdentities.inverseBlock, SquareMatrix.Blocks.block_ll,
    SquareMatrix.Blocks.block_lr, SquareMatrix.Blocks.block_rl, SquareMatrix.matrixOfFn_apply] at equal
  rw [← FiniteSum.Fin.sumFin_add] at equal
  apply (FiniteSum.Fin.sumFin_congr (fun index => by ring1)).trans (equal.trans ?_)
  by_cases same : row = column
  · rw [if_pos same, if_pos same.symm]
  · rw [if_neg same, if_neg (Ne.symm same)]

end Purelib.LinearAlgebra.Matrix.Inverse.SymplecticBlockIdentities

end
