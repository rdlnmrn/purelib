module
meta import Purelib.Elab.ConstructiveInjectivity
-- Exposed scans retain the original dependent zero-entry certificates.
public import Purelib.Data.Fin
public import Purelib.Data.Gaussian.Field
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Blocks
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Compute
import Purelib.LinearAlgebra.Matrix.Schur

public import Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic

open Purelib

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

@[expose] public section

/-!
# A selected-pivot inverse for a fixed finite rational matrix

For a fixed exact matrix, decidable pivot selection is harmless.  Unlike the
polynomial all-pivot aggregation needed by the synchronized approximation
layer, this constructor follows only one nonzero pivot at each size.  Existing
finite Schur and unpivoting identities verify the result.  The approximation
algorithms and their continuity/movement guarantees are unchanged.
-/

namespace Purelib.LinearAlgebra.Matrix.Inverse.ExactPivotInverse

open Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse

set_option genInjectivity false in
/-- A finite row scan retains a nonzero entry or certifies every entry zero.

The found outcome carries the original bounded column and its nonvanishing
witness. Exhaustion carries a proposition for each coordinate of the same row. -/
private inductive RowSearch {count :
  Nat} (row : Fin count -> SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) where
  /-- Retain a bounded column and the nonvanishing of its original row entry. -/ | found (column : Fin count) (nonzero :
    row column ≠ 0)
  /-- Certify that every entry of the original row is zero. -/ | zero (allZero : forall column, row column = 0)

constructive_injectivity RowSearch

/-- Scan a Gaussian row from its first bounded coordinate for a nonzero entry.

Exhaustion returns pointwise zero certificates for the original row. -/
private def searchRow : {count : Nat}
  -> (row : Fin count -> SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) ->
  Purelib.LinearAlgebra.Matrix.Inverse.ExactPivotInverse.RowSearch row
  | 0, _ => .zero fun column => Fin.elim0 column
  | count + 1, row => by
      by_cases zero : row 0 = 0
      · cases Purelib.LinearAlgebra.Matrix.Inverse.ExactPivotInverse.searchRow (fun column : Fin
          count => row column.succ) with
        | found column nonzero => exact .found column.succ nonzero
        | zero tailZero => exact .zero (fun column => Data.Fin.cases_induction zero tailZero column)
      · exact .found 0 zero

set_option genInjectivity false in
/-- A finite matrix scan retains a nonzero entry or pointwise zero certificates.

The selected row and column bound the exact original matrix entry. The zero
outcome retains its vanishing proposition at every original pair of indices. -/
private inductive MatrixSearch {rows
  columns : Nat}
    (matrix : Fin rows -> Fin columns -> SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) where
  /-- Retain bounded row and column indices and nonvanishing of their original entry. -/ | found (row : Fin rows)
    (column : Fin columns) (nonzero : matrix row column ≠ 0)
  /-- Certify that every entry of the original matrix is zero. -/ | zero (allZero : forall row column, matrix row column
    = 0)

constructive_injectivity MatrixSearch

/-- Scan matrix rows in order and retain the first certified nonzero coordinate pair.

If every row scan is zero, the result certifies that every original matrix entry vanishes. -/
private def searchMatrix {columns :
  Nat} : {rows : Nat} ->
    (matrix : Fin rows -> Fin columns -> SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) ->
      Purelib.LinearAlgebra.Matrix.Inverse.ExactPivotInverse.MatrixSearch matrix
  | 0, _ => .zero fun row => Fin.elim0 row
  | rows + 1, matrix => by
      cases Purelib.LinearAlgebra.Matrix.Inverse.ExactPivotInverse.searchRow (matrix 0) with
      | found column nonzero => exact .found 0 column nonzero
      | zero headZero =>
          cases Purelib.LinearAlgebra.Matrix.Inverse.ExactPivotInverse.searchMatrix (fun row : Fin
            rows => matrix row.succ) with
          | found row column nonzero => exact .found row.succ column nonzero
          | zero tailZero => exact .zero (fun row => Data.Fin.cases_induction headZero tailZero row)

set_option genInjectivity false in
/-- A row pivot scan retains a nonzero bounded column or certifies the row zero.

The original row indexes both alternatives. Nonvanishing concerns its same
selected entry, while the zero outcome retains every coordinate proposition. -/
inductive PivotRowScan {count : Nat}
  (row : Fin count -> SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) where
  /-- Retain a bounded column and the nonvanishing of its original row entry. -/ | found (column : Fin count) (nonzero :
    row column ≠ 0)
  /-- Certify that every entry of the original row is zero. -/ | zero (allZero : forall column, row column = 0)

constructive_injectivity PivotRowScan

/-- Scan bounded row coordinates in order for a nonzero Gaussian pivot.

The result retains the original row and certifies either its selected entry or complete vanishing. -/
def scanRowForPivot : {count : Nat} ->
  (row : Fin count -> SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) ->
  SquareMatrix.Inverse.ExactPivotInverse.PivotRowScan row
  | 0, _ => .zero fun column => Fin.elim0 column
  | count + 1, row => by
      by_cases zero : row 0 = 0
      · cases Purelib.LinearAlgebra.Matrix.Inverse.ExactPivotInverse.scanRowForPivot (fun column :
          Fin count => row column.succ) with
        | found column nonzero => exact .found column.succ nonzero
        | zero tailZero => exact .zero (fun column => Data.Fin.cases_induction zero tailZero column)
      · exact .found 0 zero

set_option genInjectivity false in
/-- A matrix pivot scan retains nonzero entry indices or pointwise vanishing.

Both finite coordinates belong to the original matrix carrier. Exhaustion
retains vanishing at every row and column rather than choosing a replacement matrix. -/
inductive PivotMatrixScan {rows
  columns : Nat}
    (matrix : Fin rows -> Fin columns -> SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) where
  /-- Retain bounded row and column indices and nonvanishing of their original entry. -/ | found (row : Fin rows)
    (column : Fin columns) (nonzero : matrix row column ≠ 0)
  /-- Certify that every entry of the original matrix is zero. -/ | zero (allZero : forall row column, matrix row column
    = 0)

constructive_injectivity PivotMatrixScan

/-- Scan the finite matrix in row order for an explicit nonzero pivot.

Every unsuccessful row retains a zero certificate, so exhaustion certifies the whole original matrix. -/
def scanMatrixForPivot {columns : Nat}
  : {rows : Nat} ->
    (matrix : Fin rows -> Fin columns -> SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) ->
      SquareMatrix.Inverse.ExactPivotInverse.PivotMatrixScan matrix
  | 0, _ => .zero fun row => Fin.elim0 row
  | rows + 1, matrix => by
      cases SquareMatrix.Inverse.ExactPivotInverse.scanRowForPivot (matrix 0) with
      | found column nonzero => exact .found 0 column nonzero
      | zero headZero =>
          cases Purelib.LinearAlgebra.Matrix.Inverse.ExactPivotInverse.scanMatrixForPivot (fun row :
            Fin rows => matrix row.succ) with
          | found row column nonzero => exact .found row.succ column nonzero
          | zero tailZero => exact .zero (fun row => Data.Fin.cases_induction headZero tailZero row)

set_option genInjectivity false in
/-- A retained pivot consists of two bounded indices and their nonzero matrix entry.

The original finite row-and-column scan supplies both coordinates. The
nonvanishing certificate concerns exactly the same original matrix entry. -/
structure Pivot {size : Nat} (matrix :
  SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1)) where
  /-- The bounded original row of the selected nonzero entry. -/ row : Fin (size + 1)
  /-- The bounded original column of the selected nonzero entry. -/ column : Fin (size + 1)
  /-- The retained original entry at these two indices is nonzero. -/ nonzero : matrix row column ≠ 0

constructive_injectivity Pivot

open Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse in
/-- Select a nonzero entry of a nonempty matrix with trivial left kernel.

The finite scan supplies the retained indices; triviality rules out its all-zero outcome. -/
def selectPivot {size : Nat} (matrix :
  SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1))
    (trivial : SquareMatrix.Inverse.PivotedScaledInverse.LeftKernelTrivial matrix) :
      SquareMatrix.Inverse.ExactPivotInverse.Pivot matrix := by
  cases SquareMatrix.Inverse.ExactPivotInverse.scanMatrixForPivot (fun row column => matrix row column) with
  | found row column nonzero => exact ⟨row, column, nonzero⟩
  | zero allZero =>
      have impossible : False := by
        rcases exists_nonzero_entry_of_leftKernelTrivial matrix trivial with
          ⟨row, column, nonzero⟩
        exact nonzero (allZero row column)
      exact impossible.elim

set_option genInjectivity false in
/-- An exact finite inverse retains its scaled-inverse data and nonzero scalar.

The original matrix indexes both multiplication identities. Its same retained
scalar is certified nonzero, without changing the computed inverse entries. -/
structure NonzeroInverse {size : Nat}
  (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square size) where
  /-- The computed scaled inverse of the original matrix, with both multiplication identities. -/ inverse :
    SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverse matrix
  /-- The retained inverse scalar is nonzero. -/ scalar_nonzero : inverse.scalar ≠ 0

constructive_injectivity NonzeroInverse

/-- One finite pivot scan and one smaller inverse per recursive stage.
Nonvanishing descends through the fraction-free Schur complement; no search
success or determinant-separation premise is left for the caller. -/
def invert : {size : Nat} -> (matrix :
  SquareMatrix.Inverse.PivotedScaledInverse.Square size) ->
    SquareMatrix.Inverse.PivotedScaledInverse.LeftKernelTrivial matrix ->
      SquareMatrix.Inverse.ExactPivotInverse.NonzeroInverse matrix
  | 0, matrix, _ =>
      { inverse := SquareMatrix.Inverse.Scaled.Compute.scaledInverse matrix
        scalar_nonzero := by change (1 : SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) ≠ 0; decide }
  | size + 1, matrix, trivial => by
      let pivot := SquareMatrix.Inverse.ExactPivotInverse.selectPivot matrix trivial
      let pivoted := SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix matrix pivot.row pivot.column
      have pivotedTrivial : SquareMatrix.Inverse.PivotedScaledInverse.LeftKernelTrivial pivoted :=
        SquareMatrix.Inverse.PivotedScaledInverse.leftKernelTrivial_pivotMatrix trivial pivot.row pivot.column
      have headNonzero : SquareMatrix.Blocks.head pivoted ≠ 0 := by
        simpa only [pivoted, SquareMatrix.Blocks.head,
          SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix,
            SquareMatrix.Inverse.PivotedScaledInverse.swapColumns_apply,
            SquareMatrix.Inverse.PivotedScaledInverse.swapRows_apply,
            SquareMatrix.Inverse.PivotedScaledInverse.swapZero_zero] using pivot.nonzero
      let smaller := Purelib.LinearAlgebra.Matrix.Inverse.ExactPivotInverse.invert
        (SquareMatrix.Schur.schur pivoted)
        (SquareMatrix.Inverse.PivotedScaledInverse.leftKernelTrivial_schur_of_head_nonzero pivoted pivotedTrivial
          headNonzero)
      refine
        { inverse := SquareMatrix.Inverse.PivotedScaledInverse.pivotBranch matrix pivot.row pivot.column smaller.inverse
          scalar_nonzero := ?_ }
      change SquareMatrix.Blocks.head pivoted * smaller.inverse.scalar ≠ 0
      exact Data.Gaussian.Field.mul_ne_zero_direct
        headNonzero smaller.scalar_nonzero

end Purelib.LinearAlgebra.Matrix.Inverse.ExactPivotInverse
