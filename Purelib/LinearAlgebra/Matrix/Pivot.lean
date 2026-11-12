module

public import Purelib.Data.Fin
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Certified finite pivot scans

The original row-ordered scan returns its first nonzero entry or certifies
that every original entry is zero. Only coefficient equality and zero are used.
-/

@[expose] public section

namespace Purelib.LinearAlgebra.Matrix.Pivot

open Purelib

variable {K : Type*} [Zero K]

set_option genInjectivity false in
/-- A retained pivot consists of bounded indices and their original nonzero matrix entry.

Both coordinates belong to the original rectangular table. The selected
coefficient, rather than a copied scalar or a replacement table, indexes its
nonvanishing certificate.
-/
structure Entry {rows columns : Nat} (matrix : Fin rows → Fin columns → K) where
  /-- The bounded original row of the selected nonzero coefficient. -/
  row : Fin rows
  /-- The bounded original column of the selected nonzero coefficient. -/
  column : Fin columns
  /-- The selected coefficient in the original table is nonzero. -/
  nonzero : matrix row column ≠ 0

constructive_injectivity Entry

variable [DecidableEq K]

set_option genInjectivity false in
/-- A row pivot scan retains a nonzero bounded column or certifies the row zero.

The original row indexes both alternatives. Nonvanishing concerns its same
selected entry, while the zero outcome retains every coordinate proposition. -/
inductive RowScan {count : Nat}
  (row : Fin count -> K) where
  /-- Retain a bounded column and the nonvanishing of its original row entry. -/ | found (column : Fin count) (nonzero :
    row column ≠ 0)
  /-- Certify that every entry of the original row is zero. -/ | zero (allZero : forall column, row column = 0)

constructive_injectivity RowScan

/-- Scan bounded row coordinates in order for a nonzero K pivot.

The result retains the original row and certifies either its selected entry or complete vanishing. -/
def scanRow : {count : Nat} ->
  (row : Fin count -> K) ->
  RowScan row
  | 0, _ => .zero fun column => Fin.elim0 column
  | count + 1, row => by
      by_cases zero : row 0 = 0
      · cases Pivot.scanRow (fun column :
          Fin count => row column.succ) with
        | found column nonzero => exact .found column.succ nonzero
        | zero tailZero => exact .zero (fun column => Data.Fin.cases_induction zero tailZero column)
      · exact .found 0 zero

set_option genInjectivity false in
/-- A matrix pivot scan retains nonzero entry indices or pointwise vanishing.

Both finite coordinates belong to the original matrix carrier. Exhaustion
retains vanishing at every row and column rather than choosing a replacement matrix. -/
inductive MatrixScan {rows
  columns : Nat}
    (matrix : Fin rows -> Fin columns -> K) where
  /-- Retain bounded row and column indices and nonvanishing of their original entry. -/ | found (row : Fin rows)
    (column : Fin columns) (nonzero : matrix row column ≠ 0)
  /-- Certify that every entry of the original matrix is zero. -/ | zero (allZero : forall row column, matrix row column
    = 0)

constructive_injectivity MatrixScan

/-- Scan the finite matrix in row order for an explicit nonzero pivot.

Every unsuccessful row retains a zero certificate, so exhaustion certifies the whole original matrix. -/
def scan {columns : Nat}
  : {rows : Nat} ->
    (matrix : Fin rows -> Fin columns -> K) ->
      MatrixScan matrix
  | 0, _ => .zero fun row => Fin.elim0 row
  | rows + 1, matrix => by
      cases scanRow (matrix 0) with
      | found column nonzero => exact .found 0 column nonzero
      | zero headZero =>
          cases Pivot.scan (fun row :
            Fin rows => matrix row.succ) with
          | found row column nonzero => exact .found row.succ column nonzero
          | zero tailZero => exact .zero (fun row => Data.Fin.cases_induction headZero tailZero row)

end Purelib.LinearAlgebra.Matrix.Pivot
