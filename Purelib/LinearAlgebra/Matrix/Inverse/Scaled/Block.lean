module
import Purelib.Data.Fin
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Blocks
public import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
public import Purelib.LinearAlgebra.Matrix.Schur
import Purelib.LinearAlgebra.Vector.Dot
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

/-!
# Fraction-free finite matrix inversion

Vectors and matrices are dimension-indexed structural `Vector` data, exposed
through entry lookup, and every sum is a fold over `List.ofFn`.  A scaled
inverse records both multiplication identities.  The block extension below
is division-free: a pivot and a scaled inverse of its Schur complement produce
a scaled inverse of the whole matrix.
-/

namespace Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Block

open Purelib
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.Vector

public section

universe u
variable {K : Type*} [CommRing K]

/-- Extend a scaled inverse of the fraction-free Schur complement to the whole matrix.

The leading pivot, cached row and column products and smaller inverse determine
all four blocks without division. Their scaled row, column and inverse data are
materialized once and consumed by every final entry read. -/
@[expose] def blockInverse {n : Nat} (matrix : SquareMatrix K (n + 1))
    (smaller : Basic.ScaledInverse (Schur.schur matrix)) : SquareMatrix K (n +
      1) :=
  let a := Blocks.head matrix
  let row := Blocks.topRow matrix
  let column := Blocks.leftColumn matrix
  let inverse := smaller.inverse
  let inverseColumn := Multiplication.matrixVector inverse column
  let rowInverse := Multiplication.vectorMatrix row inverse
  let corner := smaller.scalar + Dot.dot row inverseColumn
  let negativeHead := -a
  let headSquare := a ^ 2
  let scaledRow := Data.Vector.Basic.vectorOfFn fun index => negativeHead * rowInverse index
  let scaledColumn := Data.Vector.Basic.vectorOfFn fun index => negativeHead * inverseColumn index
  let scaledInverse := matrixOfFn fun row column => headSquare * inverse row column
  matrixOfFn fun i j => Data.Fin.cases
    (Data.Fin.cases corner (fun columnIndex => scaledRow columnIndex) j)
    (fun rowIndex => Data.Fin.cases
      (scaledColumn rowIndex)
      (fun columnIndex => scaledInverse rowIndex columnIndex) j) i

/-- Read one displayed entry of the division-free block inverse.

The original first-or-successor row and column select one of the four cached
block values. The readback uses the same finite splitter as the construction. -/
theorem blockInverse_apply {n : Nat} (matrix : SquareMatrix K (n + 1))
    (smaller : Basic.ScaledInverse (Schur.schur matrix)) (row column : Fin (n +
      1)) :
    blockInverse matrix smaller row column =
      Data.Fin.cases
        (Data.Fin.cases
          (smaller.scalar + Dot.dot (Blocks.topRow matrix)
            (Multiplication.matrixVector smaller.inverse (Blocks.leftColumn matrix)))
          (fun columnIndex =>
            -Blocks.head matrix * Multiplication.vectorMatrix (Blocks.topRow
              matrix) smaller.inverse
              columnIndex) column)
        (fun rowIndex => Data.Fin.cases
          (-Blocks.head matrix * Multiplication.matrixVector smaller.inverse
            (Blocks.leftColumn matrix)
            rowIndex)
          (fun columnIndex =>
            Blocks.head matrix ^ 2 * smaller.inverse rowIndex columnIndex) column) row := by
  unfold blockInverse
  rewrite [matrixOfFn_apply]
  revert row column
  apply Data.Fin.cases_induction
  · apply Data.Fin.cases_induction
    · rfl
    · intro index
      change (Data.Vector.Basic.vectorOfFn _ : Data.Vector _ n) index = _
      rewrite [Data.Vector.Basic.vectorOfFn_apply]
      rfl
  · intro rowIndex
    apply Data.Fin.cases_induction
    · change (Data.Vector.Basic.vectorOfFn _ : Data.Vector _ n) rowIndex = _
      rewrite [Data.Vector.Basic.vectorOfFn_apply]
      rfl
    · intro columnIndex
      change (matrixOfFn _ : SquareMatrix _ n) rowIndex columnIndex = _
      rewrite [matrixOfFn_apply]
      rfl

/-- The original matrix times the constructed block inverse is the pivot-scaled identity.

The scalar is the leading entry times the retained smaller-inverse scalar. -/
theorem mul_blockInverse {n : Nat} (matrix : SquareMatrix K (n + 1))
    (smaller : Basic.ScaledInverse (Schur.schur matrix)) :
    Multiplication.mul matrix (blockInverse matrix smaller) =
      Multiplication.scaleIdentity (Blocks.head matrix * smaller.scalar) := open
        Purelib.Algebra in by
  let a := Blocks.head matrix
  let row := Blocks.topRow matrix
  let column := Blocks.leftColumn matrix
  let remaining := Blocks.tail matrix
  let inverse := smaller.inverse
  let inverseColumn := Multiplication.matrixVector inverse column
  let rowInverse := Multiplication.vectorMatrix row inverse
  let corner := smaller.scalar + Dot.dot row inverseColumn
  have schurInverseColumn :
      Multiplication.matrixVector (Schur.schur matrix) inverseColumn =
        fun i => smaller.scalar * column i := by
    dsimp only [inverseColumn, inverse, column]
    rw [← Multiplication.matrixVector_mul, smaller.right_identity,
      Multiplication.matrixVector_scaleIdentity]
  apply matrix_ext
  intro matrixRow matrixColumn
  refine Data.Fin.cases_induction ?_ (fun rowIndex => ?_) matrixRow
  · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) matrixColumn
    · rw [Multiplication.mul_apply, Multiplication.scaleIdentity_apply,
        FiniteSum.Fin.sumFin_succ,
        blockInverse_apply matrix smaller _ _, if_pos rfl]
      rw [FiniteSum.Fin.sumFin_congr
        (right := fun i => row i * (-a * inverseColumn i))
        (fun i => by
          rw [blockInverse_apply]
          simp only [Data.Fin.cases_zero, Data.Fin.cases_succ]
          rw [show matrix (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) i.succ = row i by
            unfold row Blocks.topRow
            rewrite [Data.Vector.Basic.vectorOfFn_apply]
            exact Eq.refl _])]
      change a * corner +
          FiniteSum.Fin.sumFin (fun i => row i * (-a * inverseColumn i)) =
        a * smaller.scalar
      have summed : FiniteSum.Fin.sumFin (fun i => row i * (-a * inverseColumn i)) =
          -a * Dot.dot row inverseColumn := by
        rw [FiniteSum.Fin.sumFin_congr
          (right := fun i => -a * (row i * inverseColumn i))
          (fun _ => by ring1)]
        exact FiniteSum.Fin.sumFin_mul_left (-a) (fun i => row i * inverseColumn i)
      rw [summed]
      dsimp only [corner]
      ring1
    · rw [Multiplication.mul_apply, Multiplication.scaleIdentity_apply,
        FiniteSum.Fin.sumFin_succ,
        blockInverse_apply matrix smaller _ columnIndex.succ,
        if_neg (Ne.symm (Data.Fin.succ_ne_zero columnIndex))]
      rw [FiniteSum.Fin.sumFin_congr
        (right := fun i => row i * (a ^ 2 * inverse i columnIndex))
        (fun i => by
          rw [blockInverse_apply]
          simp only [Data.Fin.cases_succ]
          rw [show matrix (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) i.succ = row i by
            unfold row Blocks.topRow
            rewrite [Data.Vector.Basic.vectorOfFn_apply]
            exact Eq.refl _])]
      change a * (-a * rowInverse columnIndex) +
          FiniteSum.Fin.sumFin (fun i => row i *
            (a ^ 2 * inverse i columnIndex)) = 0
      rw [FiniteSum.Fin.sumFin_congr
        (right := fun i => a ^ 2 * (row i * inverse i columnIndex))
        (fun _ => by ring1)]
      rw [FiniteSum.Fin.sumFin_mul_left]
      have rowInverseAt : rowInverse columnIndex =
          FiniteSum.Fin.sumFin (fun i => row i * inverse i columnIndex) :=
        Multiplication.vectorMatrix_apply row inverse columnIndex
      rw [rowInverseAt]
      ring1
  · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) matrixColumn
    · rw [Multiplication.mul_apply, Multiplication.scaleIdentity_apply,
        FiniteSum.Fin.sumFin_succ,
        blockInverse_apply matrix smaller _ _,
        if_neg (Data.Fin.succ_ne_zero rowIndex)]
      rw [← Blocks.leftColumn_apply matrix rowIndex]
      rw [FiniteSum.Fin.sumFin_congr
        (right := fun i => remaining rowIndex i *
          (-a * inverseColumn i))
        (fun i => by
          rw [blockInverse_apply]
          simp only [Data.Fin.cases_zero, Data.Fin.cases_succ]
          rw [show matrix rowIndex.succ i.succ =
              remaining rowIndex i by
            exact (Blocks.tail_apply matrix _ _).symm])]
      change column rowIndex * corner +
          FiniteSum.Fin.sumFin (fun i => remaining rowIndex i *
            (-a * inverseColumn i)) = 0
      have summed : FiniteSum.Fin.sumFin (fun i => remaining rowIndex i *
            (-a * inverseColumn i)) =
          -a * Multiplication.matrixVector remaining inverseColumn rowIndex := by
        rw [FiniteSum.Fin.sumFin_congr
          (right := fun i => -a *
            (remaining rowIndex i * inverseColumn i))
          (fun _ => by ring1)]
        rw [Multiplication.matrixVector_apply]
        exact FiniteSum.Fin.sumFin_mul_left (-a)
          (fun i => remaining rowIndex i * inverseColumn i)
      rw [summed]
      have schurAt := Data.Vector.Basic.vector_eq_at schurInverseColumn rowIndex
      rw [Schur.matrixVector_schur] at schurAt
      simp only [Data.Vector.Basic.vectorOfFn_apply] at schurAt
      have rearranged :
          a * Multiplication.matrixVector remaining inverseColumn rowIndex =
            smaller.scalar * column rowIndex +
              column rowIndex * Dot.dot row inverseColumn := by
        calc
          a * Multiplication.matrixVector remaining inverseColumn rowIndex =
              (a * Multiplication.matrixVector remaining inverseColumn rowIndex -
                column rowIndex * Dot.dot row inverseColumn) +
                column rowIndex * Dot.dot row inverseColumn := by ring1
          _ = smaller.scalar * column rowIndex +
                column rowIndex * Dot.dot row inverseColumn := by rw [schurAt]
      rw [show -a * Multiplication.matrixVector remaining inverseColumn rowIndex =
          -(a * Multiplication.matrixVector remaining inverseColumn rowIndex) by ring1,
        rearranged]
      dsimp only [corner]
      ring1
    · rw [Multiplication.mul_apply, Multiplication.scaleIdentity_apply,
        FiniteSum.Fin.sumFin_succ,
        blockInverse_apply matrix smaller _ columnIndex.succ]
      rw [← Blocks.leftColumn_apply matrix rowIndex]
      rw [FiniteSum.Fin.sumFin_congr
        (right := fun i => remaining rowIndex i *
          (a ^ 2 * inverse i columnIndex))
        (fun i => by
          rw [blockInverse_apply]
          simp only [Data.Fin.cases_succ]
          rw [show matrix rowIndex.succ i.succ =
              remaining rowIndex i by
            exact (Blocks.tail_apply matrix _ _).symm])]
      change column rowIndex * (-a * rowInverse columnIndex) +
          FiniteSum.Fin.sumFin (fun i => remaining rowIndex i *
            (a ^ 2 * inverse i columnIndex)) =
          (if rowIndex.succ = columnIndex.succ then
          a * smaller.scalar else 0)
      rw [FiniteSum.Fin.sumFin_congr
        (right := fun i => a ^ 2 *
          (remaining rowIndex i * inverse i columnIndex))
        (fun _ => by ring1)]
      rw [FiniteSum.Fin.sumFin_mul_left]
      have schurEntry := matrix_eq_at smaller.right_identity
        rowIndex columnIndex
      have schurEntryAt : Multiplication.matrixVector (Schur.schur matrix)
          (fun i => inverse i columnIndex) rowIndex =
          (if rowIndex = columnIndex then smaller.scalar else 0) := by
        calc
          Multiplication.matrixVector (Schur.schur matrix)
                (Data.Vector.Basic.vectorOfFn fun i => inverse i columnIndex) rowIndex =
              Multiplication.mul (Schur.schur matrix) inverse rowIndex columnIndex :=
            Multiplication.matrixVector_column_eq_mul_apply (Schur.schur matrix) inverse
              rowIndex columnIndex
          _ = Multiplication.scaleIdentity smaller.scalar rowIndex columnIndex :=
            schurEntry
          _ = (if rowIndex = columnIndex then smaller.scalar else 0) :=
            Multiplication.scaleIdentity_apply smaller.scalar rowIndex columnIndex
      rw [Schur.matrixVector_schur] at schurEntryAt
      have schurEntryAlias :
          a * FiniteSum.Fin.sumFin (fun i => remaining rowIndex i * inverse i columnIndex) -
              column rowIndex *
                FiniteSum.Fin.sumFin (fun i => row i * inverse i columnIndex) =
            (if rowIndex = columnIndex then smaller.scalar else 0) := by
        rw [Multiplication.matrixVector_column_apply remaining inverse rowIndex columnIndex,
          Multiplication.dot_column_apply row inverse columnIndex] at schurEntryAt
        change a * FiniteSum.Fin.sumFin (fun i => remaining rowIndex i *
              inverse i columnIndex) -
            column rowIndex *
              FiniteSum.Fin.sumFin (fun i => row i * inverse i columnIndex) =
          (if rowIndex = columnIndex then smaller.scalar else 0) at schurEntryAt
        exact schurEntryAt
      have rowInverseAt : rowInverse columnIndex =
          FiniteSum.Fin.sumFin (fun i => row i * inverse i columnIndex) :=
        Multiplication.vectorMatrix_apply row inverse columnIndex
      rw [rowInverseAt]
      by_cases equal : rowIndex = columnIndex
      · have successorEqual : rowIndex.succ = columnIndex.succ :=
          congrArg Fin.succ equal
        rw [if_pos equal] at schurEntryAlias
        rw [if_pos successorEqual]
        calc
          column rowIndex *
                (-a * FiniteSum.Fin.sumFin (fun i => row i * inverse i columnIndex)) +
              a ^ 2 *
                FiniteSum.Fin.sumFin (fun i => remaining rowIndex i * inverse i columnIndex) =
              a * (a *
                FiniteSum.Fin.sumFin (fun i => remaining rowIndex i * inverse i columnIndex) -
                column rowIndex *
                  FiniteSum.Fin.sumFin (fun i => row i * inverse i columnIndex)) := by ring1
          _ = a * smaller.scalar := by rw [schurEntryAlias]
      · have successorNe : rowIndex.succ ≠ columnIndex.succ := by
          intro successorEqual
          exact equal (Fin.ext (Nat.succ.inj
            (congrArg Fin.val successorEqual)))
        rw [if_neg equal] at schurEntryAlias
        rw [if_neg successorNe]
        calc
          column rowIndex *
                (-a * FiniteSum.Fin.sumFin (fun i => row i * inverse i columnIndex)) +
              a ^ 2 *
                FiniteSum.Fin.sumFin (fun i => remaining rowIndex i * inverse i columnIndex) =
              a * (a *
                FiniteSum.Fin.sumFin (fun i => remaining rowIndex i * inverse i columnIndex) -
                column rowIndex *
                  FiniteSum.Fin.sumFin (fun i => row i * inverse i columnIndex)) := by ring1
          _ = a * 0 := by rw [schurEntryAlias]
          _ = 0 := mul_zero a

/-- The constructed block inverse times the original matrix is the pivot-scaled identity.

The scalar is the leading entry times the retained smaller-inverse scalar. -/
theorem blockInverse_mul {n : Nat} (matrix : SquareMatrix K (n + 1))
    (smaller : Basic.ScaledInverse (Schur.schur matrix)) :
    Multiplication.mul (blockInverse matrix smaller) matrix =
      Multiplication.scaleIdentity (Blocks.head matrix * smaller.scalar) := open
        Purelib.Algebra in by
  let a := Blocks.head matrix
  let row := Blocks.topRow matrix
  let column := Blocks.leftColumn matrix
  let remaining := Blocks.tail matrix
  let inverse := smaller.inverse
  let inverseColumn := Multiplication.matrixVector inverse column
  let rowInverse := Multiplication.vectorMatrix row inverse
  let corner := smaller.scalar + Dot.dot row inverseColumn
  have rowInverseSchur :
      Multiplication.vectorMatrix rowInverse (Schur.schur matrix) =
        fun j => row j * smaller.scalar := by
    dsimp only [rowInverse, inverse, row]
    rw [← Multiplication.vectorMatrix_mul, smaller.left_identity,
      Multiplication.vectorMatrix_scaleIdentity]
  have cornerDot : Dot.dot rowInverse column = Dot.dot row inverseColumn := by
    exact Multiplication.dot_vectorMatrix_matrixVector row inverse column
  apply matrix_ext
  intro matrixRow matrixColumn
  refine Data.Fin.cases_induction ?_ (fun rowIndex => ?_) matrixRow
  · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) matrixColumn
    · rw [Multiplication.mul_apply, Multiplication.scaleIdentity_apply,
        FiniteSum.Fin.sumFin_succ,
        blockInverse_apply matrix smaller _ _, if_pos rfl]
      rw [FiniteSum.Fin.sumFin_congr
        (right := fun i => (-a * rowInverse i) * column i)
        (fun i => by
          rw [blockInverse_apply]
          simp only [Data.Fin.cases_zero, Data.Fin.cases_succ]
          rw [show matrix i.succ (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) = column i by
            unfold column Blocks.leftColumn
            rewrite [Data.Vector.Basic.vectorOfFn_apply]
            exact Eq.refl _])]
      change corner * a +
          FiniteSum.Fin.sumFin (fun i => (-a * rowInverse i) * column i) =
        a * smaller.scalar
      have summed : FiniteSum.Fin.sumFin (fun i => (-a * rowInverse i) * column i) =
          -a * Dot.dot rowInverse column := by
        rw [FiniteSum.Fin.sumFin_congr
          (right := fun i => -a * (rowInverse i * column i))
          (fun _ => by ring1)]
        exact FiniteSum.Fin.sumFin_mul_left (-a) (fun i => rowInverse i * column i)
      rw [summed, cornerDot]
      dsimp only [corner]
      ring1
    · rw [Multiplication.mul_apply, Multiplication.scaleIdentity_apply,
        FiniteSum.Fin.sumFin_succ,
        blockInverse_apply matrix smaller _ _,
        if_neg (Ne.symm (Data.Fin.succ_ne_zero columnIndex))]
      rw [← Blocks.topRow_apply matrix columnIndex]
      rw [FiniteSum.Fin.sumFin_congr
        (right := fun i => (-a * rowInverse i) *
          remaining i columnIndex)
        (fun i => by
          rw [blockInverse_apply]
          simp only [Data.Fin.cases_zero, Data.Fin.cases_succ]
          rw [show matrix i.succ columnIndex.succ =
              remaining i columnIndex by
            exact (Blocks.tail_apply matrix _ _).symm])]
      change corner * row columnIndex +
          FiniteSum.Fin.sumFin (fun i => (-a * rowInverse i) *
            remaining i columnIndex) = 0
      have summed : FiniteSum.Fin.sumFin (fun i => (-a * rowInverse i) *
            remaining i columnIndex) =
          -a * Multiplication.vectorMatrix rowInverse remaining columnIndex := by
        rw [FiniteSum.Fin.sumFin_congr
          (right := fun i => -a *
            (rowInverse i * remaining i columnIndex))
          (fun _ => by ring1)]
        rw [Multiplication.vectorMatrix_apply]
        exact FiniteSum.Fin.sumFin_mul_left (-a)
          (fun i => rowInverse i * remaining i columnIndex)
      rw [summed]
      have schurAt := Data.Vector.Basic.vector_eq_at rowInverseSchur columnIndex
      rw [Schur.vectorMatrix_schur] at schurAt
      simp only [Data.Vector.Basic.vectorOfFn_apply] at schurAt
      have schurAtAlias :
          a * Multiplication.vectorMatrix rowInverse remaining columnIndex -
              Dot.dot rowInverse column * row columnIndex =
            row columnIndex * smaller.scalar := by
        simpa only [a, remaining, column, row] using schurAt
      have rearranged :
          a * Multiplication.vectorMatrix rowInverse remaining columnIndex =
            row columnIndex * smaller.scalar +
              Dot.dot rowInverse column * row columnIndex := by
        calc
          a * Multiplication.vectorMatrix rowInverse remaining columnIndex =
              (a * Multiplication.vectorMatrix rowInverse remaining columnIndex -
                Dot.dot rowInverse column * row columnIndex) +
                Dot.dot rowInverse column * row columnIndex := by ring1
          _ = row columnIndex * smaller.scalar +
                Dot.dot rowInverse column * row columnIndex := by
              rw [schurAtAlias]
      rw [show -a * Multiplication.vectorMatrix rowInverse remaining columnIndex =
          -(a * Multiplication.vectorMatrix rowInverse remaining columnIndex) by ring1,
        rearranged]
      dsimp only [corner]
      rw [← cornerDot]
      ring1
  · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) matrixColumn
    · rw [Multiplication.mul_apply, Multiplication.scaleIdentity_apply,
        FiniteSum.Fin.sumFin_succ,
        blockInverse_apply matrix smaller rowIndex.succ _,
        if_neg (Data.Fin.succ_ne_zero rowIndex)]
      rw [FiniteSum.Fin.sumFin_congr
        (right := fun i => (a ^ 2 * inverse rowIndex i) * column i)
        (fun i => by
          rw [blockInverse_apply]
          simp only [Data.Fin.cases_succ]
          rw [show matrix i.succ (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) = column i by
            unfold column Blocks.leftColumn
            rewrite [Data.Vector.Basic.vectorOfFn_apply]
            exact Eq.refl _])]
      change (-a * inverseColumn rowIndex) * a +
          FiniteSum.Fin.sumFin (fun i => (a ^ 2 * inverse rowIndex i) * column i) = 0
      rw [FiniteSum.Fin.sumFin_congr
        (right := fun i => a ^ 2 * (inverse rowIndex i * column i))
        (fun _ => by ring1)]
      rw [FiniteSum.Fin.sumFin_mul_left]
      have inverseColumnAt : inverseColumn rowIndex =
          FiniteSum.Fin.sumFin (fun i => inverse rowIndex i * column i) :=
        Multiplication.matrixVector_apply inverse column rowIndex
      rw [inverseColumnAt]
      ring1
    · rw [Multiplication.mul_apply, Multiplication.scaleIdentity_apply,
        FiniteSum.Fin.sumFin_succ,
        blockInverse_apply matrix smaller rowIndex.succ _]
      rw [← Blocks.topRow_apply matrix columnIndex]
      rw [FiniteSum.Fin.sumFin_congr
        (right := fun i => (a ^ 2 * inverse rowIndex i) *
          remaining i columnIndex)
        (fun i => by
          rw [blockInverse_apply]
          simp only [Data.Fin.cases_succ]
          rw [show matrix i.succ columnIndex.succ =
              remaining i columnIndex by
            exact (Blocks.tail_apply matrix _ _).symm])]
      change (-a * inverseColumn rowIndex) * row columnIndex +
          FiniteSum.Fin.sumFin (fun i => (a ^ 2 * inverse rowIndex i) *
            remaining i columnIndex) =
          (if rowIndex.succ = columnIndex.succ then
          a * smaller.scalar else 0)
      rw [FiniteSum.Fin.sumFin_congr
        (right := fun i => a ^ 2 *
          (inverse rowIndex i * remaining i columnIndex))
        (fun _ => by ring1)]
      rw [FiniteSum.Fin.sumFin_mul_left]
      have schurEntry := matrix_eq_at smaller.left_identity
        rowIndex columnIndex
      have schurEntryAt : Multiplication.vectorMatrix (fun i => inverse rowIndex i)
          (Schur.schur matrix) columnIndex =
          (if rowIndex = columnIndex then smaller.scalar else 0) := by
        calc
          Multiplication.vectorMatrix (Data.Vector.Basic.vectorOfFn fun i => inverse rowIndex i)
                (Schur.schur matrix) columnIndex =
              Multiplication.mul inverse (Schur.schur matrix) rowIndex columnIndex :=
            Multiplication.vectorMatrix_row_eq_mul_apply inverse (Schur.schur matrix)
              rowIndex columnIndex
          _ = Multiplication.scaleIdentity smaller.scalar rowIndex columnIndex :=
            schurEntry
          _ = (if rowIndex = columnIndex then smaller.scalar else 0) :=
            Multiplication.scaleIdentity_apply smaller.scalar rowIndex columnIndex
      rw [Schur.vectorMatrix_schur] at schurEntryAt
      have schurEntryAlias :
          a * FiniteSum.Fin.sumFin (fun i => inverse rowIndex i *
                remaining i columnIndex) -
              FiniteSum.Fin.sumFin (fun i => inverse rowIndex i * column i) *
                row columnIndex =
            (if rowIndex = columnIndex then smaller.scalar else 0) := by
        rw [Multiplication.vectorMatrix_row_apply inverse remaining rowIndex columnIndex,
          Multiplication.dot_row_apply inverse rowIndex column] at schurEntryAt
        change a * FiniteSum.Fin.sumFin (fun i => inverse rowIndex i *
              remaining i columnIndex) -
            FiniteSum.Fin.sumFin (fun i => inverse rowIndex i * column i) *
              row columnIndex =
          (if rowIndex = columnIndex then smaller.scalar else 0) at schurEntryAt
        exact schurEntryAt
      have inverseColumnAt : inverseColumn rowIndex =
          FiniteSum.Fin.sumFin (fun i => inverse rowIndex i * column i) :=
        Multiplication.matrixVector_apply inverse column rowIndex
      rw [inverseColumnAt]
      by_cases equal : rowIndex = columnIndex
      · have successorEqual : rowIndex.succ = columnIndex.succ :=
          congrArg Fin.succ equal
        rw [if_pos equal] at schurEntryAlias
        rw [if_pos successorEqual]
        calc
          (-a * FiniteSum.Fin.sumFin (fun i => inverse rowIndex i * column i)) *
                row columnIndex +
              a ^ 2 * FiniteSum.Fin.sumFin (fun i => inverse rowIndex i *
                remaining i columnIndex) =
              a * (a * FiniteSum.Fin.sumFin (fun i => inverse rowIndex i *
                remaining i columnIndex) -
                FiniteSum.Fin.sumFin (fun i => inverse rowIndex i * column i) *
                  row columnIndex) := by ring1
          _ = a * smaller.scalar := by rw [schurEntryAlias]
      · have successorNe : rowIndex.succ ≠ columnIndex.succ := by
          intro successorEqual
          exact equal (Fin.ext (Nat.succ.inj
            (congrArg Fin.val successorEqual)))
        rw [if_neg equal] at schurEntryAlias
        rw [if_neg successorNe]
        calc
          (-a * FiniteSum.Fin.sumFin (fun i => inverse rowIndex i * column i)) *
                row columnIndex +
              a ^ 2 * FiniteSum.Fin.sumFin (fun i => inverse rowIndex i *
                remaining i columnIndex) =
              a * (a * FiniteSum.Fin.sumFin (fun i => inverse rowIndex i *
                remaining i columnIndex) -
                FiniteSum.Fin.sumFin (fun i => inverse rowIndex i * column i) *
                  row columnIndex) := by ring1
          _ = a * 0 := by rw [schurEntryAlias]
          _ = 0 := mul_zero a

/-- Extend a two-sided scaled inverse by the division-free block formula.

The original pivot multiplies the retained smaller scalar. The block matrix
retains the same smaller inverse and both finite multiplication certificates. -/
@[expose] def extendScaledInverse {n : Nat} (matrix : SquareMatrix K (n + 1))
    (smaller : Basic.ScaledInverse (Schur.schur matrix)) :
      Basic.ScaledInverse matrix where
  scalar := Blocks.head matrix * smaller.scalar
  inverse := blockInverse matrix smaller
  left_identity := blockInverse_mul matrix smaller
  right_identity := mul_blockInverse matrix smaller
end

end Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Block
