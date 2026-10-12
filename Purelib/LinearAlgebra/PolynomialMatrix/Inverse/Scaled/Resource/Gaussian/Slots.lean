module

import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Block
public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Compute
public import Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Slots

import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Resource.Slots

import Purelib.Polynomial.Dense.Multiplication
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Fin
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Multiplication
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-!
# Retained polynomial inverse resource envelopes

The original Schur and block recurrences retain their scalar, inverse and coefficient
data. Slot and magnitude certificates bound those same stored polynomials.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Slots

open Purelib
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra
open Purelib.Polynomial

public section

/-- A shared coefficient-list length bound for the retained inverse scalar and matrix.

Both components are the original stored outputs of the inverse computation. The certificate bounds each scalar and
matrix-entry coefficient list with the same natural allowance. -/
structure DataSlotsWithin {count : Nat} (data :
  Basic.GaussianScaledInverseData count)
    (slots : Nat) : Prop where
  /-- The retained scalar coefficient list fits within the shared slot allowance. -/ scalar : data.scalar.coeffs.length
    ≤ slots
  /-- Every retained inverse-entry coefficient list fits within the shared slot allowance. -/ inverse :
    PolynomialMatrix.Resource.Gaussian.Slots.MatrixSlotsWithin data.inverse slots

/-- Compute the recursive coefficient-slot envelope for polynomial inverse data.

A positive-dimensional step doubles the input slot allowance and adds the corresponding smaller envelope. -/
@[expose] def dataSlotEnvelope : Nat → Nat → Nat
  | 0, _ => 1
  | count + 1, slots =>
      2 * slots + Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Slots.dataSlotEnvelope count
        (2 * slots)

/-- Every polynomial Schur entry uses at most twice the original matrix slot bound.

The original head, tail, left-column and top-row polynomials supply the two Schur products. Their normalized difference
uses at most twice the original maximum entry allowance. -/
theorem schur_slots {count : Nat} (matrix : Basic.GaussianNumberMatrix (count + 1))
    (row column : Fin count) :
    (PolynomialMatrix.Basic.schur matrix row column).coeffs.length ≤
      2 * PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound matrix := by
  let first := PolynomialMatrix.Basic.head matrix *
    PolynomialMatrix.Basic.tail matrix row column
  let second := PolynomialMatrix.Basic.leftColumn matrix row *
    PolynomialMatrix.Basic.topRow matrix column
  have headDegree :
      (PolynomialMatrix.Basic.head matrix).degreeCount ≤
        PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound matrix :=
    (Dense.Gaussian.Resource.Slots.degreeCount_le_coeffs_length _).trans
      (PolynomialMatrix.Resource.Gaussian.Slots.matrixSlot_le matrix 0 0)
  have tailDegree :
      (PolynomialMatrix.Basic.tail matrix row column).degreeCount ≤
        PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound matrix :=
    (Dense.Gaussian.Resource.Slots.degreeCount_le_coeffs_length _).trans (by
      simpa only [PolynomialMatrix.Basic.tail,
        SquareMatrix.matrixOfFn_apply, -eq_self, -iff_self] using
        PolynomialMatrix.Resource.Gaussian.Slots.matrixSlot_le matrix row.succ column.succ)
  have leftDegree :
      (PolynomialMatrix.Basic.leftColumn matrix row).degreeCount ≤
        PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound matrix :=
    (Dense.Gaussian.Resource.Slots.degreeCount_le_coeffs_length _).trans (by
      simpa only [PolynomialMatrix.Basic.leftColumn,
        Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] using
        PolynomialMatrix.Resource.Gaussian.Slots.matrixSlot_le matrix row.succ 0)
  have topDegree :
      (PolynomialMatrix.Basic.topRow matrix column).degreeCount ≤
        PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound matrix :=
    (Dense.Gaussian.Resource.Slots.degreeCount_le_coeffs_length _).trans (by
      simpa only [PolynomialMatrix.Basic.topRow,
        Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] using
        PolynomialMatrix.Resource.Gaussian.Slots.matrixSlot_le matrix 0 column.succ)
  have firstDegree : first.degreeCount ≤ 2 * PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound matrix := by
    refine (Dense.Basic.DensePolynomial.degreeCount_mul_le _ _).trans ((Nat.sub_le _ _).trans ?_)
    calc
      (PolynomialMatrix.Basic.head matrix).degreeCount +
            (PolynomialMatrix.Basic.tail matrix row column).degreeCount ≤
          PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound matrix +
            PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound matrix :=
        Nat.add_le_add headDegree tailDegree
      _ = 2 * PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound matrix := by omega0
  have secondDegree : second.degreeCount ≤ 2 * PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound matrix := by
    refine (Dense.Basic.DensePolynomial.degreeCount_mul_le _ _).trans ((Nat.sub_le _ _).trans ?_)
    calc
      (PolynomialMatrix.Basic.leftColumn matrix row).degreeCount +
            (PolynomialMatrix.Basic.topRow matrix column).degreeCount ≤
          PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound matrix +
            PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound matrix :=
        Nat.add_le_add leftDegree topDegree
      _ = 2 * PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound matrix := by omega0
  have differenceDegree : (first - second).degreeCount ≤
      max first.degreeCount second.degreeCount :=
    Dense.Basic.DensePolynomial.degreeCount_sub_le_of_normalized (Dense.Basic.DensePolynomial.normalize_mul _ _)
  have normalized : (first - second).normalize = first - second :=
    Dense.Basic.DensePolynomial.normalize_sub _ _
  simp only [PolynomialMatrix.Basic.schur,
    SquareMatrix.matrixOfFn_apply, -eq_self, -iff_self]
  change (first - second).coeffs.length ≤ _
  change (first - second).normalize.coeffs.length ≤ _ at differenceDegree
  rw [normalized] at differenceDegree
  exact differenceDegree.trans ((Data.Nat.Order.max_eq_natMax _ _).symm ▸ Data.Nat.Order.max_le firstDegree
    secondDegree)

/-- The recursive polynomial inverse scalar and matrix satisfy the computed slot envelope.

The assumption bounds each original matrix coefficient list by the supplied slot allowance. -/
theorem scaledInverseData_slots :
    ∀ (count : Nat) (matrix : Basic.GaussianNumberMatrix count) (slots : Nat),
      PolynomialMatrix.Resource.Gaussian.Slots.MatrixSlotsWithin matrix slots →
      PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Slots.DataSlotsWithin
        (PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData count matrix)
        (PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Slots.dataSlotEnvelope count slots)
  | 0, _, _, _ => by
      constructor
      · rfl
      · intro row
        exact Fin.elim0 row
  | count + 1, matrix, slots, matrixWithin => by
      let schurMatrix := PolynomialMatrix.Basic.schur matrix
      have schurWithin : PolynomialMatrix.Resource.Gaussian.Slots.MatrixSlotsWithin schurMatrix (2 * slots) := by
        intro row column
        exact (PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Slots.schur_slots matrix row column).trans
          (Nat.mul_le_mul_left 2 (PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound_le matrixWithin))
      let smaller := PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData
        count schurMatrix
      have smallerWithin : PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Slots.DataSlotsWithin smaller
          (PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Slots.dataSlotEnvelope count (2 * slots)) :=
        Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Slots.scaledInverseData_slots count
          schurMatrix (2 * slots) schurWithin
      let recursiveSlots := PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Slots.dataSlotEnvelope count (2 * slots)
      change PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Slots.DataSlotsWithin
        (PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData (count + 1) matrix)
        (2 * slots + recursiveSlots)
      have headSlots :
          (PolynomialMatrix.Basic.head matrix).coeffs.length ≤
            slots := matrixWithin 0 0
      have smallerScalarSlots : smaller.scalar.coeffs.length ≤
          recursiveSlots := smallerWithin.scalar
      have scalarSlots :
          (PolynomialMatrix.Basic.head matrix * smaller.scalar).coeffs.length ≤
            2 * slots + recursiveSlots :=
        (Purelib.Polynomial.Dense.Gaussian.Resource.Slots.mul_slots _ _).trans (calc
          (PolynomialMatrix.Basic.head matrix).coeffs.length +
                smaller.scalar.coeffs.length ≤ slots + recursiveSlots :=
            Nat.add_le_add headSlots smallerScalarSlots
          _ ≤ 2 * slots + recursiveSlots := by
            apply Nat.add_le_add_right
            rw [Nat.two_mul]
            exact Nat.le_add_right slots slots)
      constructor
      · exact scalarSlots
      · intro row column
        let a := PolynomialMatrix.Basic.head matrix
        let top := PolynomialMatrix.Basic.topRow matrix
        let left := PolynomialMatrix.Basic.leftColumn matrix
        let inverse := smaller.inverse
        have aSlots : a.coeffs.length ≤ slots := matrixWithin 0 0
        have topSlots : ∀ index, (top index).coeffs.length ≤ slots :=
          fun index => by
            simpa only [top, PolynomialMatrix.Basic.topRow,
              Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] using
              matrixWithin 0 index.succ
        have leftSlots : ∀ index, (left index).coeffs.length ≤ slots :=
          fun index => by
            simpa only [left, PolynomialMatrix.Basic.leftColumn,
              Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] using
              matrixWithin index.succ 0
        have inverseSlots : ∀ i j,
            (inverse i j).coeffs.length ≤ recursiveSlots :=
          smallerWithin.inverse
        have inverseColumnSlots : ∀ index,
            (PolynomialMatrix.Basic.matrixVector inverse left index
                ).coeffs.length ≤ recursiveSlots + slots := by
          intro index
          simpa only [PolynomialMatrix.Basic.matrixVector,
            Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] using
            Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Slots.dot_slots (inverse index) left
              recursiveSlots slots
              (fun middle => inverseSlots index middle) leftSlots
        have rowInverseSlots : ∀ index,
            (PolynomialMatrix.Basic.vectorMatrix top inverse index
                ).coeffs.length ≤ slots + recursiveSlots := by
          intro index
          simpa only [PolynomialMatrix.Basic.vectorMatrix,
            Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] using
            Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Slots.dot_slots top
              (Data.Vector.Basic.vectorOfFn fun middle =>
                inverse middle index)
              slots recursiveSlots topSlots
              (fun middle => by
                simpa only [Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] using
                  inverseSlots middle index)
        unfold PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData
          PolynomialMatrix.Inverse.Scaled.Block.blockInverse
        simp only [SquareMatrix.matrixOfFn_apply, -eq_self, -iff_self]
        refine Data.Fin.cases_induction ?_ (fun rowIndex => ?_) row
        · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) column
          · have innerDot := Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Slots.dot_slots top
                (PolynomialMatrix.Basic.matrixVector inverse left)
                slots (recursiveSlots + slots) topSlots inverseColumnSlots
            exact (Purelib.Polynomial.Dense.Gaussian.Resource.Slots.add_slots smaller.scalar _).trans (by
              rw [Data.Nat.Order.max_eq_natMax]
              apply Data.Nat.Order.max_le
              · exact smallerWithin.scalar.trans
                  (Nat.le_add_left recursiveSlots (2 * slots))
              · exact innerDot.trans (Nat.le_of_eq (by omega0)))
          · have negA := Purelib.Polynomial.Dense.Gaussian.Resource.Slots.neg_slots a
            have rowBound := rowInverseSlots columnIndex
            exact (Purelib.Polynomial.Dense.Gaussian.Resource.Slots.mul_slots (-a)
              (PolynomialMatrix.Basic.vectorMatrix top inverse
                columnIndex)).trans (calc
                  (-a).coeffs.length +
                      (PolynomialMatrix.Basic.vectorMatrix top
                        inverse columnIndex).coeffs.length ≤
                    slots + (slots + recursiveSlots) :=
                      Nat.add_le_add (negA.trans aSlots) rowBound
                  _ = 2 * slots + recursiveSlots := by omega0)
        · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) column
          · have negA := Purelib.Polynomial.Dense.Gaussian.Resource.Slots.neg_slots a
            have columnBound := inverseColumnSlots rowIndex
            exact (Purelib.Polynomial.Dense.Gaussian.Resource.Slots.mul_slots (-a)
              (PolynomialMatrix.Basic.matrixVector inverse left
                rowIndex)).trans (calc
                  (-a).coeffs.length +
                      (PolynomialMatrix.Basic.matrixVector inverse
                        left rowIndex).coeffs.length ≤
                    slots + (recursiveSlots + slots) :=
                      Nat.add_le_add (negA.trans aSlots) columnBound
                  _ = 2 * slots + recursiveSlots := by omega0)
          · have square := Purelib.Polynomial.Dense.Gaussian.Resource.Slots.mul_slots a a
            have inverseBound := inverseSlots rowIndex columnIndex
            exact (Purelib.Polynomial.Dense.Gaussian.Resource.Slots.mul_slots (a * a) (inverse rowIndex
              columnIndex)).trans
              (calc
                (a * a).coeffs.length +
                      (inverse rowIndex columnIndex).coeffs.length ≤
                    (slots + slots) + recursiveSlots :=
                  Nat.add_le_add
                    (square.trans (Nat.add_le_add aSlots aSlots)) inverseBound
                _ = 2 * slots + recursiveSlots := by omega0)

/-! ## Coefficient magnitudes -/

end

end Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Slots
