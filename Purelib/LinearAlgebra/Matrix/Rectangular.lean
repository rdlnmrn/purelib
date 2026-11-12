module

public import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Vector.Dot
public import Purelib.Data.Vector.Split
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Purelib.Tactic.QuotientFreeOmega

/-!
# Rectangular structural matrices

Rectangles reuse the original structural row and vector data. Entry lookup,
transpose and matrix-vector products retain both finite dimensions.
-/

public section

namespace Purelib.LinearAlgebra.Matrix

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.Vector
open Purelib.Algebra.FiniteSum.Fin
open Purelib.LinearAlgebra.Vector.Dot

/-- A rectangle is the original structural vector of fixed-width structural rows. -/
abbrev Rectangular (K : Type*) (rows columns : Nat) := Vec (Vec K columns) rows

namespace Rectangular

variable {K : Type*}

/-- Retain a rectangular entry table as original structural row data. -/
@[expose] def ofFn {rows columns : Nat} (entries : Fin rows → Fin columns → K) :
    Rectangular K rows columns :=
  vectorOfFn fun row => vectorOfFn (entries row)

/-- Reading a retained rectangular entry recovers its original table entry. -/
theorem ofFn_apply {rows columns : Nat} (entries : Fin rows → Fin columns → K)
    (row : Fin rows) (column : Fin columns) :
    ofFn entries row column = entries row column := by
  rw [ofFn, vectorOfFn_apply, vectorOfFn_apply]

/-- Equal entries identify the same original structural rectangle. -/
theorem ext {rows columns : Nat} {first second : Rectangular K rows columns}
    (equal : ∀ row column, first row column = second row column) : first = second := by
  apply vector_ext
  intro row
  apply vector_ext
  exact equal row

/-- Transport the same original structural rectangle along equality of its two retained dimensions. -/
@[expose] def cast {rows columns otherRows otherColumns : Nat}
    (rowSize : rows = otherRows) (columnSize : columns = otherColumns)
    (matrix : Rectangular K rows columns) : Rectangular K otherRows otherColumns :=
  rowSize ▸ columnSize ▸ matrix

/-- A dimension transport preserves every same-valued original finite coordinate. -/
theorem cast_at {rows columns otherRows otherColumns : Nat}
    (rowSize : rows = otherRows) (columnSize : columns = otherColumns)
    (matrix : Rectangular K rows columns) (row : Fin otherRows) (column : Fin otherColumns) :
    cast rowSize columnSize matrix row column =
      matrix ⟨row.val, rowSize.symm ▸ row.isLt⟩ ⟨column.val, columnSize.symm ▸ column.isLt⟩ := by
  cases rowSize
  cases columnSize
  rfl

/-- Retain one original column as a structural vector at the original row dimension. -/
@[expose] def column {rows columns : Nat} (matrix : Rectangular K rows columns)
    (index : Fin columns) : Vec K rows :=
  vectorOfFn fun row => matrix row index

/-- Reading a retained column recovers the same original matrix entry. -/
theorem column_at {rows columns : Nat} (matrix : Rectangular K rows columns)
    (index : Fin columns) (row : Fin rows) : column matrix index row = matrix row index :=
  vectorOfFn_apply _ _

/-- Exchange the retained row and column dimensions and their original entries. -/
@[expose] def transpose {rows columns : Nat} (matrix : Rectangular K rows columns) :
    Rectangular K columns rows :=
  ofFn fun row column => matrix column row

/-- A transposed entry is the same original entry with exchanged coordinates. -/
theorem transpose_apply {rows columns : Nat} (matrix : Rectangular K rows columns)
    (row : Fin columns) (column : Fin rows) :
    transpose matrix row column = matrix column row := ofFn_apply _ _ _

/-- Two transposes recover the complete retained original matrix. -/
theorem transpose_transpose {rows columns : Nat} (matrix : Rectangular K rows columns) :
    transpose (transpose matrix) = matrix := by
  apply ext
  intro row column
  rw [transpose_apply, transpose_apply]

/-- Retain the initial original rows by cutting their same structural outer vector. -/
@[expose] def takeRows {rows columns cut : Nat} (bound : cut ≤ rows)
    (matrix : Rectangular K rows columns) : Rectangular K cut columns := Split.take bound matrix

/-- An initial-row lookup reads the same original row and column. -/
theorem takeRows_at {rows columns cut : Nat} (bound : cut ≤ rows)
    (matrix : Rectangular K rows columns) (row : Fin cut) (column : Fin columns) :
    takeRows bound matrix row column = matrix ⟨row.val, Nat.lt_of_lt_of_le row.isLt bound⟩ column :=
  congrArg (fun values : Vec K columns => values column) (Split.take_apply bound matrix row)

/-- Retain the initial columns of the same original rectangular matrix. -/
@[expose] def takeColumns {rows columns cut : Nat} (bound : cut ≤ columns)
    (matrix : Rectangular K rows columns) : Rectangular K rows cut :=
  vectorOfFn fun row => Split.take bound (matrix row)

/-- Retain the final columns of the same original rectangular matrix. -/
@[expose] def dropColumns {rows columns cut : Nat} (bound : cut ≤ columns)
    (matrix : Rectangular K rows columns) : Rectangular K rows (columns - cut) :=
  vectorOfFn fun row => Split.drop bound (matrix row)

/-- Reading an initial column preserves its original row and column entry. -/
theorem takeColumns_at {rows columns cut : Nat} (bound : cut ≤ columns)
    (matrix : Rectangular K rows columns) (row : Fin rows) (column : Fin cut) :
    takeColumns bound matrix row column = matrix row ⟨column.val, Nat.lt_of_lt_of_le column.isLt bound⟩ := by
  rw [takeColumns, vectorOfFn_apply, Split.take_apply]

/-- Reading a final column preserves its original shifted column entry. -/
theorem dropColumns_at {rows columns cut : Nat} (bound : cut ≤ columns)
    (matrix : Rectangular K rows columns) (row : Fin rows) (column : Fin (columns - cut)) :
    dropColumns bound matrix row column = matrix row ⟨cut + column.val, by have := column.isLt; omega0⟩ := by
  rw [dropColumns, vectorOfFn_apply, Split.drop_apply]

section

variable [CommRing K]

/-- Multiply rectangles by the original structural row-dot and column materialization kernel.

The shared middle dimension bounds the same finite dot product used by square
matrix multiplication. Both outer dimensions remain independently indexed.
-/
@[expose] def mul {rows middle columns : Nat} (left : Rectangular K rows middle)
    (right : Rectangular K middle columns) : Rectangular K rows columns :=
  ofFn fun row column => dot (left row) (vectorOfFn fun index => right index column)

/-- A rectangular product entry is its original finite row-column sum. -/
theorem mul_at {rows middle columns : Nat} (left : Rectangular K rows middle)
    (right : Rectangular K middle columns) (row : Fin rows) (column : Fin columns) :
    mul left right row column = sumFin (fun index => left row index * right index column) := by
  rw [mul, ofFn_apply]
  unfold dot
  apply sumFin_congr
  intro index
  rw [vectorOfFn_apply]

/-- Rectangular multiplication associates at its original four finite dimensions. -/
theorem mul_assoc {firstSize secondSize thirdSize fourthSize : Nat}
    (first : Rectangular K firstSize secondSize) (second : Rectangular K secondSize thirdSize)
    (third : Rectangular K thirdSize fourthSize) :
    mul (mul first second) third = mul first (mul second third) := by
  apply ext
  intro row column
  rw [mul_at (mul first second) third row column,
    mul_at first (mul second third) row column]
  have leftExpansion : sumFin (fun middle => mul first second row middle * third middle column) =
      sumFin (fun middle => sumFin (fun inner => first row inner * second inner middle) *
        third middle column) := by
    apply sumFin_congr
    intro middle
    rw [mul_at]
  have rightExpansion : sumFin (fun inner => first row inner * mul second third inner column) =
      sumFin (fun inner => first row inner * sumFin (fun middle => second inner middle * third middle column)) := by
    apply sumFin_congr
    intro inner
    rw [mul_at]
  rw [leftExpansion, rightExpansion]
  calc
    _ = sumFin (fun middle => sumFin (fun inner =>
        (first row inner * second inner middle) * third middle column)) := by
      apply sumFin_congr
      intro middle
      exact (sumFin_mul_right _ _).symm
    _ = sumFin (fun inner => sumFin (fun middle =>
        (first row inner * second inner middle) * third middle column)) := sumFin_swap _
    _ = _ := by
      apply sumFin_congr
      intro inner
      rw [← sumFin_mul_left]
      apply sumFin_congr
      intro middle
      exact _root_.mul_assoc _ _ _

/-- Cutting the initial original product rows commutes with the same rectangular multiplication. -/
theorem takeRows_mul {rows middle columns cut : Nat} (bound : cut ≤ rows)
    (left : Rectangular K rows middle) (right : Rectangular K middle columns) :
    takeRows bound (mul left right) = mul (takeRows bound left) right := by
  apply ext
  intro row column
  rw [takeRows_at, mul_at, mul_at]
  apply sumFin_congr
  intro index
  rw [takeRows_at]

/-- Cutting the initial original product columns commutes with the same rectangular multiplication. -/
theorem takeColumns_mul {rows middle columns cut : Nat} (bound : cut ≤ columns)
    (left : Rectangular K rows middle) (right : Rectangular K middle columns) :
    takeColumns bound (mul left right) = mul left (takeColumns bound right) := by
  apply ext
  intro row column
  rw [takeColumns_at, mul_at, mul_at]
  apply sumFin_congr
  intro index
  rw [takeColumns_at]

/-- Multiply a structural rectangle by a vector over its original column dimension. -/
@[expose] def apply {rows columns : Nat} (matrix : Rectangular K rows columns)
    (values : Vec K columns) : Vec K rows :=
  vectorOfFn fun row => sumFin fun column => matrix row column * values column

/-- A rectangular matrix-vector product reads the same finite row dot product. -/
theorem apply_at {rows columns : Nat} (matrix : Rectangular K rows columns)
    (values : Vec K columns) (row : Fin rows) :
    apply matrix values row = sumFin (fun column => matrix row column * values column) :=
  vectorOfFn_apply _ _

/-- Acting on an original column reads the same column of the actual matrix product. -/
theorem apply_column {rows middle columns : Nat} (left : Rectangular K rows middle)
    (right : Rectangular K middle columns) (index : Fin columns) :
    apply left (column right index) = column (mul left right) index := by
  apply vector_ext
  intro row
  rw [apply_at, column_at, mul_at]
  apply sumFin_congr
  intro position
  rw [column_at]

/-- A rectangular action sends the structural zero vector to structural zero. -/
theorem apply_zero {rows columns : Nat} (matrix : Rectangular K rows columns) :
    apply matrix (vectorOfFn fun _ => 0) = vectorOfFn (fun _ => 0) := by
  apply vector_ext
  intro row
  rw [apply_at, vectorOfFn_apply]
  calc
    _ = sumFin (fun _ : Fin columns => (0 : K)) := by
      apply sumFin_congr
      intro column
      rw [vectorOfFn_apply, mul_zero]
    _ = 0 := sumFin_zero

/-- A rectangular action preserves the coordinate sum of two structural vectors. -/
theorem apply_add {rows columns : Nat} (matrix : Rectangular K rows columns)
    (left right : Vec K columns) :
    apply matrix (vectorOfFn fun column => left column + right column) =
      vectorOfFn (fun row => apply matrix left row + apply matrix right row) := by
  apply vector_ext
  intro row
  rw [apply_at, vectorOfFn_apply, apply_at, apply_at, ← sumFin_add]
  apply sumFin_congr
  intro column
  rw [vectorOfFn_apply, mul_add]

/-- A finite sum splits at a supplied bound without changing its original indices. -/
private theorem sum_split_at {size cut : Nat} (bound : cut ≤ size) (values : Fin size → K) :
    sumFin values =
      sumFin (fun index : Fin cut => values ⟨index.val, Nat.lt_of_lt_of_le index.isLt bound⟩) +
      sumFin (fun index : Fin (size - cut) => values ⟨cut + index.val, by have := index.isLt; omega0⟩) := by
  obtain ⟨remaining, equal⟩ := Nat.exists_eq_add_of_le bound
  subst size
  have transported : ∀ (tail : Nat) (tailEqual : tail = remaining),
      sumFin values =
        sumFin (fun index : Fin cut => values (Fin.castAdd remaining index)) +
        sumFin (fun index : Fin tail => values
          ⟨cut + index.val, Nat.add_lt_add_left (tailEqual ▸ index.isLt) cut⟩) := by
    intro tail tailEqual
    cases tailEqual
    exact sumFin_split values
  exact transported (cut + remaining - cut) (Nat.add_sub_cancel_left cut remaining)

/-- Acting on two joined coordinate blocks sums the actions of the same original column blocks. -/
theorem apply_join {rows columns cut : Nat} (bound : cut ≤ columns)
    (matrix : Rectangular K rows columns) (first : Vec K cut) (second : Vec K (columns - cut)) :
    apply matrix (Split.join bound first second) =
      vectorOfFn (fun row => apply (takeColumns bound matrix) first row +
        apply (dropColumns bound matrix) second row) := by
  apply vector_ext
  intro row
  rw [apply_at, vectorOfFn_apply, apply_at, apply_at, sum_split_at bound]
  congr 1
  · apply sumFin_congr
    intro column
    rw [Split.join_apply_take, takeColumns_at]
  · apply sumFin_congr
    intro column
    rw [Split.join_apply_drop, dropColumns_at]

/-- Transposing an actual rectangular product reverses its two original factors. -/
theorem transpose_mul {rows middle columns : Nat} (left : Rectangular K rows middle)
    (right : Rectangular K middle columns) :
    transpose (mul left right) = mul (transpose right) (transpose left) := by
  apply ext
  intro row column
  rw [transpose_apply, mul_at left right column row,
    mul_at (transpose right) (transpose left) row column]
  apply sumFin_congr
  intro index
  rw [transpose_apply, transpose_apply]
  exact _root_.mul_comm _ _

/-- A rectangular product acts by the same two successive finite vector actions. -/
theorem apply_mul {rows middle columns : Nat} (left : Rectangular K rows middle)
    (right : Rectangular K middle columns) (values : Vec K columns) :
    apply (mul left right) values = apply left (apply right values) := by
  apply vector_ext
  intro row
  rw [apply_at (mul left right) values row, apply_at left (apply right values) row]
  have leftExpansion : sumFin (fun column => mul left right row column * values column) =
      sumFin (fun column => sumFin (fun inner => left row inner * right inner column) * values column) := by
    apply sumFin_congr
    intro column
    rw [mul_at]
  have rightExpansion : sumFin (fun inner => left row inner * apply right values inner) =
      sumFin (fun inner => left row inner * sumFin (fun column => right inner column * values column)) := by
    apply sumFin_congr
    intro inner
    rw [apply_at]
  rw [leftExpansion, rightExpansion]
  calc
    _ = sumFin (fun column => sumFin (fun inner =>
        (left row inner * right inner column) * values column)) := by
      apply sumFin_congr
      intro column
      exact (sumFin_mul_right _ _).symm
    _ = sumFin (fun inner => sumFin (fun column =>
        (left row inner * right inner column) * values column)) := sumFin_swap _
    _ = _ := by
      apply sumFin_congr
      intro inner
      rw [← sumFin_mul_left]
      apply sumFin_congr
      intro column
      exact _root_.mul_assoc _ _ _

end
end Rectangular
end Purelib.LinearAlgebra.Matrix
