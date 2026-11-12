module

public import Purelib.LinearAlgebra.Matrix.Blocks
public import Purelib.LinearAlgebra.Matrix.Rectangular.Identity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Tactic.Ring

/-!
# Retained rectangular borders

A leading scalar, row and column surround the original retained tail. Diagonal
extensions preserve the cached tail and the original structural product.
-/

public section

namespace Purelib.LinearAlgebra.Matrix.Blocks

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Algebra.FiniteSum.Fin

variable {K : Type*} {rows columns : Nat}

/-- Surround a retained rectangle by one scalar, its top row and left column.

The original tail rows are retained as the tails of the new rows. The leading
column is combined with those same rows in one structural traversal.
-/
@[expose] def border (corner : K) (top : Vec K columns) (left : Vec K rows)
    (remaining : Rectangular K rows columns) : Rectangular K (rows + 1) (columns + 1) :=
  .cons (.cons corner top) (Vec.zipWith (fun value row => .cons value row) left remaining)

/-- Read the retained scalar at the leading position of a border. -/
theorem border_zero_zero (corner : K) (top : Vec K columns) (left : Vec K rows)
    (remaining : Rectangular K rows columns) : border corner top left remaining 0 0 = corner := rfl

/-- Read the retained top row at an original successor column. -/
theorem border_zero_succ (corner : K) (top : Vec K columns) (left : Vec K rows)
    (remaining : Rectangular K rows columns) (column : Fin columns) :
    border corner top left remaining 0 column.succ = top column := rfl

/-- Read the retained left column at an original successor row. -/
theorem border_succ_zero (corner : K) (top : Vec K columns) (left : Vec K rows)
    (remaining : Rectangular K rows columns) (row : Fin rows) :
    border corner top left remaining row.succ 0 = left row := by
  change (Vec.zipWith (fun value tail => Vec.cons value tail) left remaining row) 0 = left row
  rw [zipWith_apply]
  rfl

/-- Read the same retained tail entry at its two successor coordinates. -/
theorem border_succ_succ (corner : K) (top : Vec K columns) (left : Vec K rows)
    (remaining : Rectangular K rows columns) (row : Fin rows) (column : Fin columns) :
    border corner top left remaining row.succ column.succ = remaining row column := by
  change (Vec.zipWith (fun value tail => Vec.cons value tail) left remaining row) column.succ = _
  rw [zipWith_apply]
  rfl

/-- Four original boundary and tail entry families identify a nonempty rectangle.

Both dimensions split at their same first coordinate. Equality of the corner,
top row, left column and remaining original entries determines the complete
retained structural matrix.
-/
theorem ext {first second : Rectangular K (rows + 1) (columns + 1)}
    (corner : first 0 0 = second 0 0)
    (top : ∀ column : Fin columns, first 0 column.succ = second 0 column.succ)
    (left : ∀ row : Fin rows, first row.succ 0 = second row.succ 0)
    (remaining : ∀ row : Fin rows, ∀ column : Fin columns,
      first row.succ column.succ = second row.succ column.succ) : first = second := by
  apply Rectangular.ext
  intro row column
  refine Purelib.Data.Fin.cases_induction ?_ (fun row => ?_) row
  · refine Purelib.Data.Fin.cases_induction ?_ (fun column => ?_) column
    · change first 0 0 = second 0 0
      exact corner
    · change first 0 column.succ = second 0 column.succ
      exact top column
  · refine Purelib.Data.Fin.cases_induction ?_ (fun column => ?_) column
    · change first row.succ 0 = second row.succ 0
      exact left row
    · exact remaining row column

section

variable [CommRing K]

/-- Extend an original rectangle by one leading scalar and zero off-diagonal borders. -/
@[expose] def diagonal (corner : K) (remaining : Rectangular K rows columns) :
    Rectangular K (rows + 1) (columns + 1) :=
  border corner (vectorOfFn fun _ => 0) (vectorOfFn fun _ => 0) remaining

/-- The leading entry of a diagonal extension is its retained scalar. -/
theorem diagonal_zero_zero (corner : K) (remaining : Rectangular K rows columns) :
    diagonal corner remaining 0 0 = corner := rfl

/-- Every remaining entry in the leading row of a diagonal extension is zero. -/
theorem diagonal_zero_succ (corner : K) (remaining : Rectangular K rows columns)
    (column : Fin columns) : diagonal corner remaining 0 column.succ = 0 := by
  exact vectorOfFn_apply _ _

/-- Every remaining entry in the leading column of a diagonal extension is zero. -/
theorem diagonal_succ_zero (corner : K) (remaining : Rectangular K rows columns)
    (row : Fin rows) : diagonal corner remaining row.succ 0 = 0 := by
  rw [diagonal, border_succ_zero, vectorOfFn_apply]

/-- The diagonal extension retains each original tail entry exactly. -/
theorem diagonal_succ_succ (corner : K) (remaining : Rectangular K rows columns)
    (row : Fin rows) (column : Fin columns) :
    diagonal corner remaining row.succ column.succ = remaining row column := by
  exact border_succ_succ _ _ _ _ _ _

/-- The product of two diagonal extensions extends their same original tail product. -/
theorem diagonal_mul {middle : Nat} (firstCorner secondCorner : K)
    (first : Rectangular K rows middle) (second : Rectangular K middle columns) :
    Rectangular.mul (diagonal firstCorner first) (diagonal secondCorner second) =
      diagonal (firstCorner * secondCorner) (Rectangular.mul first second) := by
  apply Rectangular.ext
  intro row column
  refine Purelib.Data.Fin.cases_induction ?_ (fun row => ?_) row
  · refine Purelib.Data.Fin.cases_induction ?_ (fun column => ?_) column
    · change Rectangular.mul (diagonal firstCorner first) (diagonal secondCorner second) 0 0 =
        diagonal (firstCorner * secondCorner) (Rectangular.mul first second) 0 0
      rw [Rectangular.mul_at, sumFin_succ, diagonal_zero_zero, diagonal_zero_zero,
        diagonal_zero_zero]
      have vanishes : sumFin (fun index : Fin middle =>
          diagonal firstCorner first 0 index.succ * diagonal secondCorner second index.succ 0) = 0 := by
        rw [sumFin_congr (right := fun _ => (0 : K)) (fun index => by
          rw [diagonal_zero_succ, diagonal_succ_zero]
          exact mul_zero 0), sumFin_zero]
      rw [vanishes]
      exact add_zero _
    · change Rectangular.mul (diagonal firstCorner first) (diagonal secondCorner second) 0 column.succ =
        diagonal (firstCorner * secondCorner) (Rectangular.mul first second) 0 column.succ
      rw [Rectangular.mul_at, sumFin_succ, diagonal_zero_zero, diagonal_zero_succ,
        diagonal_zero_succ]
      have vanishes : sumFin (fun index : Fin middle =>
          diagonal firstCorner first 0 index.succ *
            diagonal secondCorner second index.succ column.succ) = 0 := by
        rw [sumFin_congr (right := fun _ => (0 : K)) (fun index => by
          rw [diagonal_zero_succ]
          exact zero_mul _), sumFin_zero]
      rw [vanishes]
      ring0
  · refine Purelib.Data.Fin.cases_induction ?_ (fun column => ?_) column
    · change Rectangular.mul (diagonal firstCorner first) (diagonal secondCorner second) row.succ 0 =
        diagonal (firstCorner * secondCorner) (Rectangular.mul first second) row.succ 0
      rw [Rectangular.mul_at, sumFin_succ, diagonal_succ_zero, diagonal_zero_zero,
        diagonal_succ_zero]
      have vanishes : sumFin (fun index : Fin middle =>
          diagonal firstCorner first row.succ index.succ * diagonal secondCorner second index.succ 0) = 0 := by
        rw [sumFin_congr (right := fun _ => (0 : K)) (fun index => by
          rw [diagonal_succ_zero]
          exact mul_zero _), sumFin_zero]
      rw [vanishes]
      ring0
    · rw [Rectangular.mul_at, sumFin_succ, diagonal_succ_zero, diagonal_zero_succ,
        diagonal_succ_succ]
      have tailProduct : sumFin (fun index : Fin middle =>
          diagonal firstCorner first row.succ index.succ *
            diagonal secondCorner second index.succ column.succ) =
          Rectangular.mul first second row column := by
        rw [Rectangular.mul_at]
        apply sumFin_congr
        intro index
        rw [diagonal_succ_succ, diagonal_succ_succ]
      rw [tailProduct]
      ring0

/-- Extending the original identity at one preserves its successor-dimensional identity. -/
theorem diagonal_unit (dimension : Nat) :
    diagonal (1 : K) (Multiplication.scaleIdentity (n := dimension) 1) =
      Multiplication.scaleIdentity 1 := by
  apply Rectangular.ext
  intro row column
  refine Purelib.Data.Fin.cases_induction ?_ (fun row => ?_) row
  · refine Purelib.Data.Fin.cases_induction ?_ (fun column => ?_) column
    · change diagonal (1 : K) (Multiplication.scaleIdentity 1) 0 0 =
        Multiplication.scaleIdentity 1 0 0
      rw [diagonal_zero_zero, Multiplication.scaleIdentity_apply, if_pos rfl]
    · change diagonal (1 : K) (Multiplication.scaleIdentity 1) 0 column.succ =
        Multiplication.scaleIdentity 1 0 column.succ
      rw [diagonal_zero_succ, Multiplication.scaleIdentity_apply,
        if_neg (fun equal => by
          have values := congrArg Fin.val equal
          change 0 = column.val + 1 at values
          exact Nat.noConfusion values)]
  · refine Purelib.Data.Fin.cases_induction ?_ (fun column => ?_) column
    · change diagonal (1 : K) (Multiplication.scaleIdentity 1) row.succ 0 =
        Multiplication.scaleIdentity 1 row.succ 0
      rw [diagonal_succ_zero, Multiplication.scaleIdentity_apply,
        if_neg (fun equal => by
          have values := congrArg Fin.val equal
          change row.val + 1 = 0 at values
          exact Nat.noConfusion values)]
    · rw [diagonal_succ_succ, Multiplication.scaleIdentity_apply, Multiplication.scaleIdentity_apply]
      by_cases equal : row = column
      · subst column
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg equal, if_neg (fun successorEqual =>
          equal (Fin.ext (Nat.succ.inj (congrArg Fin.val successorEqual))))]

end

end Purelib.LinearAlgebra.Matrix.Blocks

end
