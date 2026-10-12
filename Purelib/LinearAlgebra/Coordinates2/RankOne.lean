module

public import Purelib.LinearAlgebra.Coordinates2.Matrix
public import Purelib.Geometry.Projective.Line.Scale
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Inverse
import Purelib.Tactic.Ring

/-!
# Rank-one matrices and their two projective rulings

Nonzero singular two-by-two matrices have an executable column-times-row
factorization. Both factors are original homogeneous coordinate pairs. Their
nonzero certificates and reconstruction retain the exact input matrix.
-/

public section

namespace Purelib.LinearAlgebra.Coordinates2.Matrix

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.Inverse (inverse_eq_of_mul_eq_one)
open Purelib.Geometry.Projective.Line (Proj)
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2

variable {K : Type*} [ExplicitField K]

/-- A displayed two-by-two matrix is nonzero when at least one original entry is nonzero. -/
@[expose] def IsNonzero (matrix : Matrix2 K) : Prop :=
  matrix.a ≠ 0 ∨ matrix.b ≠ 0 ∨ matrix.c ≠ 0 ∨ matrix.d ≠ 0

/-- The original entry-based nonzero certificate is equivalent to inequality with the displayed zero matrix.

The reverse implication tests the four original scalar coordinates. No matrix
enumeration or chosen nonzero coordinate is assumed.
-/
theorem isNonzero_iff_ne_zero [DecidableEq K] (matrix : Matrix2 K) :
    matrix.IsNonzero ↔ matrix ≠ ⟨0, 0, 0, 0⟩ := by
  constructor
  · intro nonzero equal
    rcases nonzero with first | second | third | fourth
    · exact first (congrArg Matrix2.a equal)
    · exact second (congrArg Matrix2.b equal)
    · exact third (congrArg Matrix2.c equal)
    · exact fourth (congrArg Matrix2.d equal)
  · intro nonzero
    by_cases first : matrix.a ≠ 0
    · exact Or.inl first
    · by_cases second : matrix.b ≠ 0
      · exact Or.inr (Or.inl second)
      · by_cases third : matrix.c ≠ 0
        · exact Or.inr (Or.inr (Or.inl third))
        · by_cases fourth : matrix.d ≠ 0
          · exact Or.inr (Or.inr (Or.inr fourth))
          · exact False.elim (nonzero (Matrix2.ext (Decidable.byContradiction first)
              (Decidable.byContradiction second) (Decidable.byContradiction third)
              (Decidable.byContradiction fourth)))

/-- Form a column-times-row matrix from the two original homogeneous coordinate pairs. -/
@[expose] def outer (column row : Proj K) : Matrix2 K :=
  ⟨column.p * row.p, column.p * row.q, column.q * row.p, column.q * row.q⟩

/-- Every displayed column-times-row matrix is singular. -/
theorem determinant_outer (column row : Proj K) : (outer column row).determinant = 0 := by
  unfold determinant outer
  ring1

/-- Nonzero column and row factors give a nonzero matrix. -/
theorem outer_nonzero {column row : Proj K} (columnNonzero : column.Nonzero) (rowNonzero : row.Nonzero) :
    (outer column row).IsNonzero := by
  rcases columnNonzero with firstColumn | secondColumn
  · rcases rowNonzero with firstRow | secondRow
    · exact Or.inl (ExplicitField.mul_ne_zero firstColumn firstRow)
    · exact Or.inr (Or.inl (ExplicitField.mul_ne_zero firstColumn secondRow))
  · rcases rowNonzero with firstRow | secondRow
    · exact Or.inr (Or.inr (Or.inl (ExplicitField.mul_ne_zero secondColumn firstRow)))
    · exact Or.inr (Or.inr (Or.inr (ExplicitField.mul_ne_zero secondColumn secondRow)))

/-- Scaling the column and row multiplies their outer matrix by the product of the two scales. -/
theorem outer_scale_both (column row : Proj K) (columnScale rowScale : K) :
    outer (column.scale columnScale) (row.scale rowScale) =
      scalarScale (columnScale * rowScale) (outer column row) := by
  apply Matrix2.ext <;> unfold outer Proj.scale scalarScale <;> ring1

/-- Scaling only the row scales the original outer matrix by the same coefficient. -/
theorem outer_scale_row (column row : Proj K) (factor : K) :
    outer column (row.scale factor) = scalarScale factor (outer column row) := by
  apply Matrix2.ext <;> unfold outer Proj.scale scalarScale <;> ring1

/-- Scaling only the column scales the original outer matrix by the same coefficient. -/
theorem outer_scale_column (column row : Proj K) (factor : K) :
    outer (column.scale factor) row = scalarScale factor (outer column row) := by
  apply Matrix2.ext <;> unfold outer Proj.scale scalarScale <;> ring1

/-- Scaling a column and inversely scaling its row retains the original outer matrix. -/
theorem outer_reciprocal_scale (column row : Proj K) (factor : K) (factorNonzero : factor ≠ 0) :
    outer (column.scale factor) (row.scale factor⁻¹) = outer column row := by
  rw [outer_scale_both, ExplicitField.mul_inv_cancel factor factorNonzero]
  apply Matrix2.ext <;> exact one_mul _

/-- Scaling a row and inversely scaling its column retains the original outer matrix. -/
theorem outer_reciprocal_scale_row (column row : Proj K) (factor : K) (factorNonzero : factor ≠ 0) :
    outer (column.scale factor⁻¹) (row.scale factor) = outer column row := by
  rw [outer_scale_both, mul_comm factor⁻¹ factor, ExplicitField.mul_inv_cancel factor factorNonzero]
  apply Matrix2.ext <;> exact one_mul _

/-- For a fixed nonzero column, the original row coordinates inject into outer matrices. -/
theorem outer_row_injective {column left right : Proj K} (columnNonzero : column.Nonzero)
    (equal : outer column left = outer column right) : left = right := by
  apply Proj.ext
  · rcases columnNonzero with first | second
    · exact ExplicitField.eq_of_mul_eq_mul_left first (congrArg Matrix2.a equal)
    · exact ExplicitField.eq_of_mul_eq_mul_left second (congrArg Matrix2.c equal)
  · rcases columnNonzero with first | second
    · exact ExplicitField.eq_of_mul_eq_mul_left first (congrArg Matrix2.b equal)
    · exact ExplicitField.eq_of_mul_eq_mul_left second (congrArg Matrix2.d equal)

/-- For a fixed nonzero row, the original column coordinates inject into outer matrices. -/
theorem outer_column_injective {row left right : Proj K} (rowNonzero : row.Nonzero)
    (equal : outer left row = outer right row) : left = right := by
  apply Proj.ext
  · rcases rowNonzero with first | second
    · exact ExplicitField.eq_of_mul_eq_mul_right first (congrArg Matrix2.a equal)
    · exact ExplicitField.eq_of_mul_eq_mul_right second (congrArg Matrix2.b equal)
  · rcases rowNonzero with first | second
    · exact ExplicitField.eq_of_mul_eq_mul_right first (congrArg Matrix2.c equal)
    · exact ExplicitField.eq_of_mul_eq_mul_right second (congrArg Matrix2.d equal)

/-- A fixed-column outer matrix has its original two row coordinates as coefficients of the two coordinate matrices. -/
theorem outer_row_coordinates (column row : Proj K) :
    outer column row = add (scalarScale row.p (outer column ⟨1, 0⟩))
      (scalarScale row.q (outer column ⟨0, 1⟩)) := by
  apply Matrix2.ext <;> unfold outer add scalarScale <;> ring1

/-- A fixed-row outer matrix has its original two column coordinates as coefficients of the two coordinate matrices. -/
theorem outer_column_coordinates (column row : Proj K) :
    outer column row = add (scalarScale column.p (outer ⟨1, 0⟩ row))
      (scalarScale column.q (outer ⟨0, 1⟩ row)) := by
  apply Matrix2.ext <;> unfold outer add scalarScale <;> ring1

/-- Addition of the two original row coordinates gives addition of fixed-column outer matrices. -/
theorem outer_row_add (column left right : Proj K) :
    outer column ⟨left.p + right.p, left.q + right.q⟩ = add (outer column left) (outer column right) := by
  apply Matrix2.ext <;> unfold outer add <;> ring1

/-- Addition of the two original column coordinates gives addition of fixed-row outer matrices. -/
theorem outer_column_add (row left right : Proj K) :
    outer ⟨left.p + right.p, left.q + right.q⟩ row = add (outer left row) (outer right row) := by
  apply Matrix2.ext <;> unfold outer add <;> ring1

/-- A nonzero matrix distinguishes any two scalar coefficients multiplying it. -/
theorem scalarScale_factor_eq {matrix : Matrix2 K} (nonzero : matrix.IsNonzero) {left right : K}
    (equal : scalarScale left matrix = scalarScale right matrix) : left = right := by
  rcases nonzero with first | second | third | fourth
  · exact ExplicitField.eq_of_mul_eq_mul_right first (congrArg Matrix2.a equal)
  · exact ExplicitField.eq_of_mul_eq_mul_right second (congrArg Matrix2.b equal)
  · exact ExplicitField.eq_of_mul_eq_mul_right third (congrArg Matrix2.c equal)
  · exact ExplicitField.eq_of_mul_eq_mul_right fourth (congrArg Matrix2.d equal)

set_option genInjectivity false in
/-- A nonzero column-times-row factorization of one retained two-by-two matrix.

Both original homogeneous pairs, their nonzero certificates and the exact
matrix reconstruction are stored together. The matrix remains the index.
-/
structure RankOneFactorization (matrix : Matrix2 K) where
  /-- The retained nonzero column factor. -/ column : Proj K
  /-- The retained nonzero row factor. -/ row : Proj K
  /-- The column has a nonzero original coordinate. -/ columnNonzero : column.Nonzero
  /-- The row has a nonzero original coordinate. -/ rowNonzero : row.Nonzero
  /-- The retained factors reconstruct the indexed matrix exactly. -/ reconstruction : outer column row = matrix

/-- Construct a rank-one factorization by testing the original entries in column order.

The first nonzero pivot supplies a column and a normalized row. Singularity
determines the remaining entry by scalar cancellation. The last two branches
retain the zero first column and use the original second column directly.
-/
@[expose] def rankOneFactorization [DecidableEq K] (matrix : Matrix2 K)
    (oneNonzero : (1 : K) ≠ 0) (nonzero : matrix.IsNonzero) (singular : matrix.determinant = 0) :
    RankOneFactorization matrix := by
  have cross : matrix.a * matrix.d = matrix.b * matrix.c := by
    calc
      matrix.a * matrix.d = matrix.determinant + matrix.b * matrix.c := by unfold determinant; ring1
      _ = matrix.b * matrix.c := by rw [singular, zero_add]
  have mulQuotient (numerator denominator : K) (denominatorNonzero : denominator ≠ 0) :
      denominator * (numerator / denominator) = numerator := by
    calc
      denominator * (numerator / denominator) = (numerator / denominator) * denominator := mul_comm _ _
      _ = numerator := ExplicitField.div_mul_cancel numerator denominatorNonzero
  by_cases first : matrix.a ≠ 0
  · refine ⟨⟨matrix.a, matrix.c⟩, ⟨1, matrix.b / matrix.a⟩, Or.inl first, Or.inl oneNonzero, ?_⟩
    apply Matrix2.ext
    · change matrix.a * 1 = matrix.a
      exact mul_one _
    · change matrix.a * (matrix.b / matrix.a) = matrix.b
      exact mulQuotient matrix.b matrix.a first
    · change matrix.c * 1 = matrix.c
      exact mul_one _
    · change matrix.c * (matrix.b / matrix.a) = matrix.d
      apply ExplicitField.eq_of_mul_eq_mul_left first
      calc
        matrix.a * (matrix.c * (matrix.b / matrix.a)) =
            matrix.c * (matrix.a * (matrix.b / matrix.a)) := by ring1
        _ = matrix.c * matrix.b := congrArg (fun value => matrix.c * value)
          (mulQuotient matrix.b matrix.a first)
        _ = matrix.a * matrix.d := by rw [cross]; ring1
  · have firstZero : matrix.a = 0 := Decidable.byContradiction first
    by_cases third : matrix.c ≠ 0
    · refine ⟨⟨matrix.a, matrix.c⟩, ⟨1, matrix.d / matrix.c⟩, Or.inr third, Or.inl oneNonzero, ?_⟩
      have secondZero : matrix.b = 0 := by
        apply ExplicitField.eq_zero_of_mul_eq_zero_right third
        rw [← cross, firstZero, zero_mul]
      apply Matrix2.ext
      · change matrix.a * 1 = matrix.a
        exact mul_one _
      · change matrix.a * (matrix.d / matrix.c) = matrix.b
        rw [firstZero, secondZero, zero_mul]
      · change matrix.c * 1 = matrix.c
        exact mul_one _
      · change matrix.c * (matrix.d / matrix.c) = matrix.d
        exact mulQuotient matrix.d matrix.c third
    · have thirdZero : matrix.c = 0 := Decidable.byContradiction third
      by_cases second : matrix.b ≠ 0
      · refine ⟨⟨matrix.b, matrix.d⟩, ⟨0, 1⟩, Or.inl second, Or.inr oneNonzero, ?_⟩
        apply Matrix2.ext
        · change matrix.b * 0 = matrix.a
          rw [firstZero, mul_zero]
        · change matrix.b * 1 = matrix.b
          exact mul_one _
        · change matrix.d * 0 = matrix.c
          rw [thirdZero, mul_zero]
        · change matrix.d * 1 = matrix.d
          exact mul_one _
      · have secondZero : matrix.b = 0 := Decidable.byContradiction second
        have fourth : matrix.d ≠ 0 := by
          rcases nonzero with first | second | third | fourth
          · exact False.elim (first firstZero)
          · exact False.elim (second secondZero)
          · exact False.elim (third thirdZero)
          · exact fourth
        refine ⟨⟨matrix.b, matrix.d⟩, ⟨0, 1⟩, Or.inr fourth, Or.inr oneNonzero, ?_⟩
        apply Matrix2.ext
        · change matrix.b * 0 = matrix.a
          rw [firstZero, mul_zero]
        · change matrix.b * 1 = matrix.b
          exact mul_one _
        · change matrix.d * 0 = matrix.c
          rw [thirdZero, mul_zero]
        · change matrix.d * 1 = matrix.d
          exact mul_one _

/-- Equal outer matrices have equivalent original column factors if the left row is nonzero.

A nonzero row coordinate supplies equal scaled columns from the corresponding
matrix column. Scalar cancellation reflects their cross-multiplication relation.
-/
theorem outer_equal_columns {leftColumn leftRow rightColumn rightRow : Proj K}
    (rowNonzero : leftRow.Nonzero) (equal : outer leftColumn leftRow = outer rightColumn rightRow) :
    leftColumn.Equivalent rightColumn := by
  rcases rowNonzero with first | second
  · apply Proj.equivalent_of_scale_eq_scale leftColumn rightColumn leftRow.p rightRow.p first
    apply Proj.ext
    · calc
        leftRow.p * leftColumn.p = leftColumn.p * leftRow.p := mul_comm _ _
        _ = rightColumn.p * rightRow.p := congrArg Matrix2.a equal
        _ = rightRow.p * rightColumn.p := mul_comm _ _
    · calc
        leftRow.p * leftColumn.q = leftColumn.q * leftRow.p := mul_comm _ _
        _ = rightColumn.q * rightRow.p := congrArg Matrix2.c equal
        _ = rightRow.p * rightColumn.q := mul_comm _ _
  · apply Proj.equivalent_of_scale_eq_scale leftColumn rightColumn leftRow.q rightRow.q second
    apply Proj.ext
    · calc
        leftRow.q * leftColumn.p = leftColumn.p * leftRow.q := mul_comm _ _
        _ = rightColumn.p * rightRow.q := congrArg Matrix2.b equal
        _ = rightRow.q * rightColumn.p := mul_comm _ _
    · calc
        leftRow.q * leftColumn.q = leftColumn.q * leftRow.q := mul_comm _ _
        _ = rightColumn.q * rightRow.q := congrArg Matrix2.d equal
        _ = rightRow.q * rightColumn.q := mul_comm _ _

/-- Equal outer matrices have equivalent original row factors if the left column is nonzero.

A nonzero column coordinate supplies equal scaled rows from the corresponding
matrix row. The original homogeneous-pair cancellation law reflects equivalence.
-/
theorem outer_equal_rows {leftColumn leftRow rightColumn rightRow : Proj K}
    (columnNonzero : leftColumn.Nonzero) (equal : outer leftColumn leftRow = outer rightColumn rightRow) :
    leftRow.Equivalent rightRow := by
  rcases columnNonzero with first | second
  · apply Proj.equivalent_of_scale_eq_scale leftRow rightRow leftColumn.p rightColumn.p first
    exact Proj.ext (congrArg Matrix2.a equal) (congrArg Matrix2.b equal)
  · apply Proj.equivalent_of_scale_eq_scale leftRow rightRow leftColumn.q rightColumn.q second
    exact Proj.ext (congrArg Matrix2.c equal) (congrArg Matrix2.d equal)

/-- Two nonzero outer factorizations differ by exactly one nonzero column scale and its reciprocal row scale.

The original homogeneous-pair chart computes both initial scales. A retained
nonzero outer entry forces their product to be one, giving the exact reciprocal
ambiguity of the factorization. Both input columns and rows remain the owners.
-/
@[expose] def outer_scaleWitness [DecidableEq K] (leftColumn leftRow rightColumn rightRow : Proj K)
    (leftColumnNonzero : leftColumn.Nonzero) (leftRowNonzero : leftRow.Nonzero)
    (rightColumnNonzero : rightColumn.Nonzero) (rightRowNonzero : rightRow.Nonzero)
    (equal : outer leftColumn leftRow = outer rightColumn rightRow) :
    Σ' factor : K, factor ≠ 0 ∧ rightColumn = leftColumn.scale factor ∧ rightRow = leftRow.scale factor⁻¹ := by
  let columnWitness := Proj.scaleWitness leftColumn rightColumn leftColumnNonzero rightColumnNonzero
    (outer_equal_columns leftRowNonzero equal)
  let rowWitness := Proj.scaleWitness leftRow rightRow leftRowNonzero rightRowNonzero
    (outer_equal_rows leftColumnNonzero equal)
  have scaled : scalarScale 1 (outer leftColumn leftRow) =
      scalarScale (columnWitness.1 * rowWitness.1) (outer leftColumn leftRow) := by
    calc
      scalarScale 1 (outer leftColumn leftRow) = outer leftColumn leftRow := by
        apply Matrix2.ext <;> exact one_mul _
      _ = outer rightColumn rightRow := equal
      _ = outer (leftColumn.scale columnWitness.1) rightRow :=
        congrArg (fun column => outer column rightRow) columnWitness.2.2
      _ = outer (leftColumn.scale columnWitness.1) (leftRow.scale rowWitness.1) :=
        congrArg (outer (leftColumn.scale columnWitness.1)) rowWitness.2.2
      _ = scalarScale (columnWitness.1 * rowWitness.1) (outer leftColumn leftRow) :=
        outer_scale_both leftColumn leftRow columnWitness.1 rowWitness.1
  have inverse : columnWitness.1⁻¹ = rowWitness.1 := inverse_eq_of_mul_eq_one columnWitness.2.1
    (scalarScale_factor_eq (outer_nonzero leftColumnNonzero leftRowNonzero) scaled).symm
  exact ⟨columnWitness.1, columnWitness.2.1, columnWitness.2.2,
    rowWitness.2.2.trans (congrArg leftRow.scale inverse.symm)⟩

/-- The column ruling of a valid homogeneous column consists of its outer matrices with valid rows. -/
@[expose] def ColumnRuling (column : Proj K) (matrix : Matrix2 K) : Prop :=
  column.Nonzero ∧ ∃ row : Proj K, row.Nonzero ∧ outer column row = matrix

/-- The row ruling of a valid homogeneous row consists of its outer matrices with valid columns. -/
@[expose] def RowRuling (row : Proj K) (matrix : Matrix2 K) : Prop :=
  row.Nonzero ∧ ∃ column : Proj K, column.Nonzero ∧ outer column row = matrix

/-- Every column-ruling point is a nonzero singular matrix. -/
theorem ColumnRuling.nonzero_singular {column : Proj K} {matrix : Matrix2 K}
    (member : ColumnRuling column matrix) : matrix.IsNonzero ∧ matrix.determinant = 0 := by
  rcases member.2 with ⟨row, rowNonzero, reconstruction⟩
  exact ⟨(congrArg IsNonzero reconstruction).mp (outer_nonzero member.1 rowNonzero),
    (congrArg determinant reconstruction).symm.trans (determinant_outer column row)⟩

/-- Every row-ruling point is a nonzero singular matrix. -/
theorem RowRuling.nonzero_singular {row : Proj K} {matrix : Matrix2 K}
    (member : RowRuling row matrix) : matrix.IsNonzero ∧ matrix.determinant = 0 := by
  rcases member.2 with ⟨column, columnNonzero, reconstruction⟩
  exact ⟨(congrArg IsNonzero reconstruction).mp (outer_nonzero columnNonzero member.1),
    (congrArg determinant reconstruction).symm.trans (determinant_outer column row)⟩

/-- Equivalent valid column labels define the same ruling pointwise.

The original pair chart supplies a nonzero scale between the labels. Scaling
the retained row by its inverse reconstructs the same matrix with the target
column label and preserves the row's nonzero certificate.
-/
theorem column_ruling_transport [DecidableEq K] {left right : Proj K} {matrix : Matrix2 K}
    (rightNonzero : right.Nonzero) (equivalent : left.Equivalent right)
    (member : ColumnRuling left matrix) : ColumnRuling right matrix := by
  rcases member.2 with ⟨row, rowNonzero, reconstruction⟩
  let witness := Proj.scaleWitness left right member.1 rightNonzero equivalent
  refine ⟨rightNonzero, row.scale witness.1⁻¹,
    Proj.scale_nonzero (ExplicitField.inv_ne_zero witness.2.1) rowNonzero, ?_⟩
  calc
    outer right (row.scale witness.1⁻¹) = outer (left.scale witness.1) (row.scale witness.1⁻¹) :=
      congrArg (fun column => outer column (row.scale witness.1⁻¹)) witness.2.2
    _ = outer left row := outer_reciprocal_scale left row witness.1 witness.2.1
    _ = matrix := reconstruction

/-- Equivalent valid row labels define the same ruling pointwise.

The original row chart supplies the label scale. Its reciprocal scales the
retained column, reconstructing the same matrix with a nonzero target column.
-/
theorem row_ruling_transport [DecidableEq K] {left right : Proj K} {matrix : Matrix2 K}
    (rightNonzero : right.Nonzero) (equivalent : left.Equivalent right)
    (member : RowRuling left matrix) : RowRuling right matrix := by
  rcases member.2 with ⟨column, columnNonzero, reconstruction⟩
  let witness := Proj.scaleWitness left right member.1 rightNonzero equivalent
  refine ⟨rightNonzero, column.scale witness.1⁻¹,
    Proj.scale_nonzero (ExplicitField.inv_ne_zero witness.2.1) columnNonzero, ?_⟩
  calc
    outer (column.scale witness.1⁻¹) right = outer (column.scale witness.1⁻¹) (left.scale witness.1) :=
      congrArg (outer (column.scale witness.1⁻¹)) witness.2.2
    _ = outer column left := outer_reciprocal_scale_row column left witness.1 witness.2.1
    _ = matrix := reconstruction

/-- A matrix belonging to two column rulings has equivalent original column labels. -/
theorem column_ruling_labels_unique {left right : Proj K} {matrix : Matrix2 K}
    (leftMember : ColumnRuling left matrix) (rightMember : ColumnRuling right matrix) : left.Equivalent right := by
  rcases leftMember.2 with ⟨leftRow, leftRowNonzero, leftReconstruction⟩
  rcases rightMember.2 with ⟨rightRow, _, rightReconstruction⟩
  exact outer_equal_columns leftRowNonzero (leftReconstruction.trans rightReconstruction.symm)

/-- A matrix belonging to two row rulings has equivalent original row labels. -/
theorem row_ruling_labels_unique {left right : Proj K} {matrix : Matrix2 K}
    (leftMember : RowRuling left matrix) (rightMember : RowRuling right matrix) : left.Equivalent right := by
  rcases leftMember.2 with ⟨leftColumn, leftColumnNonzero, leftReconstruction⟩
  rcases rightMember.2 with ⟨rightColumn, _, rightReconstruction⟩
  exact outer_equal_rows leftColumnNonzero (leftReconstruction.trans rightReconstruction.symm)

/-- Distinct projective column labels have disjoint column rulings. -/
theorem column_rulings_disjoint {left right : Proj K} (distinct : ¬ left.Equivalent right) :
    ¬ ∃ matrix : Matrix2 K, ColumnRuling left matrix ∧ ColumnRuling right matrix := by
  rintro ⟨matrix, leftMember, rightMember⟩
  exact distinct (column_ruling_labels_unique leftMember rightMember)

/-- Distinct projective row labels have disjoint row rulings. -/
theorem row_rulings_disjoint {left right : Proj K} (distinct : ¬ left.Equivalent right) :
    ¬ ∃ matrix : Matrix2 K, RowRuling left matrix ∧ RowRuling right matrix := by
  rintro ⟨matrix, leftMember, rightMember⟩
  exact distinct (row_ruling_labels_unique leftMember rightMember)

/-- Every pair of valid column and row labels has its displayed outer matrix in both rulings. -/
theorem opposite_rulings_meet {column row : Proj K} (columnNonzero : column.Nonzero) (rowNonzero : row.Nonzero) :
    ColumnRuling column (outer column row) ∧ RowRuling row (outer column row) :=
  ⟨⟨columnNonzero, row, rowNonzero, rfl⟩, ⟨rowNonzero, column, columnNonzero, rfl⟩⟩

/-- A common point of opposite rulings is a nonzero scale of the outer matrix of their original labels.

The row factor of the supplied column-ruling point is equivalent to the
supplied row label. The original homogeneous-pair chart gives the scale;
thus the common projective point is unique with an explicit scalar witness.
-/
theorem opposite_rulings_intersection [DecidableEq K] {column row : Proj K} {matrix : Matrix2 K}
    (columnMember : ColumnRuling column matrix) (rowMember : RowRuling row matrix) :
    ∃ factor : K, factor ≠ 0 ∧ matrix = scalarScale factor (outer column row) := by
  rcases columnMember.2 with ⟨otherRow, otherRowNonzero, columnReconstruction⟩
  rcases rowMember.2 with ⟨otherColumn, _, rowReconstruction⟩
  have equivalent := outer_equal_rows columnMember.1 (columnReconstruction.trans rowReconstruction.symm)
  let witness := Proj.scaleWitness row otherRow rowMember.1 otherRowNonzero equivalent.symm
  refine ⟨witness.1, witness.2.1, ?_⟩
  calc
    matrix = outer column otherRow := columnReconstruction.symm
    _ = outer column (row.scale witness.1) := congrArg (outer column) witness.2.2
    _ = scalarScale witness.1 (outer column row) := outer_scale_row column row witness.1

/-- The row projective line parametrizes each fixed-column ruling with exactly its original projective equivalence.

Both row inputs are valid and the fixed column is nonzero. A displayed
nonzero matrix scale is reflected to row equivalence; conversely the original
row chart constructs the scale relating the two outer matrices.
-/
theorem column_ruling_parametrization [DecidableEq K] (column left right : Proj K)
    (columnNonzero : column.Nonzero) (leftNonzero : left.Nonzero) (rightNonzero : right.Nonzero) :
    (∃ factor : K, factor ≠ 0 ∧ outer column right = scalarScale factor (outer column left)) ↔
      left.Equivalent right := by
  constructor
  · rintro ⟨factor, factorNonzero, scaled⟩
    have equal : outer column (left.scale factor) = outer column right :=
      (outer_scale_row column left factor).trans scaled.symm
    exact (Proj.equivalent_scale_left_iff left right factor factorNonzero).mp
      (outer_equal_rows columnNonzero equal)
  · intro equivalent
    let witness := Proj.scaleWitness left right leftNonzero rightNonzero equivalent
    exact ⟨witness.1, witness.2.1,
      (congrArg (outer column) witness.2.2).trans (outer_scale_row column left witness.1)⟩

/-- The column projective line parametrizes each fixed-row ruling with exactly its original projective equivalence.

The fixed row and both input columns are nonzero. A matrix scale reflects to
column equivalence, and the original column chart constructs the converse scale.
-/
theorem row_ruling_parametrization [DecidableEq K] (row left right : Proj K)
    (rowNonzero : row.Nonzero) (leftNonzero : left.Nonzero) (rightNonzero : right.Nonzero) :
    (∃ factor : K, factor ≠ 0 ∧ outer right row = scalarScale factor (outer left row)) ↔
      left.Equivalent right := by
  constructor
  · rintro ⟨factor, factorNonzero, scaled⟩
    have equal : outer (left.scale factor) row = outer right row :=
      (outer_scale_column left row factor).trans scaled.symm
    exact (Proj.equivalent_scale_left_iff left right factor factorNonzero).mp
      (outer_equal_columns rowNonzero equal)
  · intro equivalent
    let witness := Proj.scaleWitness left right leftNonzero rightNonzero equivalent
    exact ⟨witness.1, witness.2.1,
      (congrArg (fun column => outer column row) witness.2.2).trans (outer_scale_column left row witness.1)⟩

end Purelib.LinearAlgebra.Coordinates2.Matrix
