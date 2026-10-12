module

import Purelib.Algebra.Field.Resource.Magnitude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Resource.Model
import Purelib.Data.Nat.Bounds.Linear

import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Block
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Compute
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Scalar
public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Slots
public import Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Magnitude

import Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Slots
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Resource.Slots

import Purelib.Polynomial.Dense.Resource
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Fin
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Multiplication
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-!
# Retained polynomial inverse resource envelopes

The original Schur and block recurrences retain their scalar, inverse and coefficient
data. Slot and magnitude certificates bound those same stored polynomials.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data

open Purelib
open Purelib.LinearAlgebra
open Purelib.Polynomial

open Purelib.Polynomial.Dense.Resource

public section

/-- A shared coefficient-magnitude bound for the retained inverse scalar and matrix.

Both components use the same Gaussian resource model and supplied natural bound. -/
structure DataWithin {count : Nat} (data :
  Basic.GaussianScaledInverseData count)
    (bound : Nat) : Prop where
  /-- Every coefficient of the retained scalar satisfies the shared magnitude bound. -/ scalar :
    Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel
    data.scalar bound
  /-- Every coefficient of every retained inverse entry satisfies the shared magnitude bound. -/ inverse :
    PolynomialMatrix.Resource.Gaussian.Magnitude.MatrixWithin data.inverse bound

/-- Compute a recursive coefficient-magnitude envelope for polynomial inverse data.

Each step pays for the Schur complement, the retained smaller slot envelope, and the block reconstruction. -/
@[expose] def dataMagnitudeEnvelope : Nat → Nat → Nat → Nat
  | 0, _, bound => bound
  | count + 1, slots, bound =>
      let schurBound := Algebra.Field.Resource.Magnitude.grow
        Purelib.Data.Gaussian.Resource.Model.gaussianModel bound
        (2 * slots + 2)
      let recursiveBound :=
        Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data.dataMagnitudeEnvelope count (2 *
        slots) schurBound
      let recursiveSlots := PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Slots.dataSlotEnvelope count (2 * slots)
      Algebra.Field.Resource.Magnitude.grow Purelib.Data.Gaussian.Resource.Model.gaussianModel
        recursiveBound
        (8 * (slots + recursiveSlots + count + 1))

/-- The inverse-data magnitude envelope is at least its supplied input bound. -/
theorem bound_le_dataMagnitudeEnvelope : ∀ count slots bound,
    bound ≤ PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data.dataMagnitudeEnvelope count slots bound
  | 0, _, _ => le_refl _
  | count + 1, slots, bound => by
      dsimp only [PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data.dataMagnitudeEnvelope, -eq_self, -iff_self]
      exact (Algebra.Field.Resource.Magnitude.bound_le_grow
        Purelib.Data.Gaussian.Resource.Model.gaussianModel bound _).trans
        ((Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data.bound_le_dataMagnitudeEnvelope
          count (2 * slots) _).trans
          (Algebra.Field.Resource.Magnitude.bound_le_grow
            Purelib.Data.Gaussian.Resource.Model.gaussianModel _ _))

/-- The computed polynomial inverse data satisfy the recursive magnitude envelope.

The input matrix has the supplied slot and coefficient bounds, and the same magnitude bound covers zero and one. -/
theorem scaledInverseData_within :
    ∀ (count : Nat) (matrix : Basic.GaussianNumberMatrix count)
      (slots bound : Nat),
      Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude 0 ≤ bound →
      Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude
        (1 : Data.Gaussian.Basic.Number) ≤ bound →
      PolynomialMatrix.Resource.Gaussian.Slots.MatrixSlotsWithin matrix slots →
      PolynomialMatrix.Resource.Gaussian.Magnitude.MatrixWithin matrix bound →
      PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data.DataWithin
        (PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData count matrix)
        (PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data.dataMagnitudeEnvelope count slots bound)
  | 0, _, _, bound, _, oneBound, _, _ => by
      constructor
      · simpa only [PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData,
          PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data.dataMagnitudeEnvelope, -eq_self, -iff_self] using
          Dense.Resource.constant_within Purelib.Data.Gaussian.Resource.Model.gaussianModel oneBound
      · intro row
        exact Fin.elim0 row
  | count + 1, matrix, slots, bound, zeroBound, oneBound, matrixSlots,
      matrixWithin => by
      let schurMatrix := PolynomialMatrix.Basic.schur matrix
      let schurBound := Algebra.Field.Resource.Magnitude.grow
        Purelib.Data.Gaussian.Resource.Model.gaussianModel bound
        (2 * slots + 2)
      have schurSlots : PolynomialMatrix.Resource.Gaussian.Slots.MatrixSlotsWithin schurMatrix (2 * slots) := by
        intro row column
        exact (PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Slots.schur_slots matrix row column).trans
          (Nat.mul_le_mul_left 2 (PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound_le matrixSlots))
      have rawSchurWithin := PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Scalar.schur_within
        zeroBound matrixWithin
      have schurWithin : PolynomialMatrix.Resource.Gaussian.Magnitude.MatrixWithin
          schurMatrix schurBound := by
        intro row column
        exact Dense.Resource.polynomialWithin_mono Purelib.Data.Gaussian.Resource.Model.gaussianModel
          (rawSchurWithin row column)
          (Algebra.Field.Resource.Magnitude.grow_mono_steps
            Purelib.Data.Gaussian.Resource.Model.gaussianModel bound
            (Nat.add_le_add_right
              (Nat.mul_le_mul_left 2 (PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound_le matrixSlots)) 2))
      let smaller := PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData
        count schurMatrix
      let recursiveBound := PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data.dataMagnitudeEnvelope count (2 *
        slots) schurBound
      let recursiveSlots := PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Slots.dataSlotEnvelope count (2 * slots)
      have smallerWithin : PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data.DataWithin smaller recursiveBound :=
        Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data.scaledInverseData_within count
          schurMatrix (2 * slots) schurBound
          (zeroBound.trans
            (Algebra.Field.Resource.Magnitude.bound_le_grow
              Purelib.Data.Gaussian.Resource.Model.gaussianModel bound _))
          (oneBound.trans
            (Algebra.Field.Resource.Magnitude.bound_le_grow
              Purelib.Data.Gaussian.Resource.Model.gaussianModel bound _))
          schurSlots schurWithin
      have smallerSlotData := PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Slots.scaledInverseData_slots count
        schurMatrix
        (2 * slots) schurSlots
      let outputSteps := 8 * (slots + recursiveSlots + count + 1)
      let outputBound := Algebra.Field.Resource.Magnitude.grow
        Purelib.Data.Gaussian.Resource.Model.gaussianModel
        recursiveBound outputSteps
      have sourceToRecursive : bound ≤ recursiveBound :=
        (Algebra.Field.Resource.Magnitude.bound_le_grow Purelib.Data.Gaussian.Resource.Model.gaussianModel
          bound _).trans
          (PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data.bound_le_dataMagnitudeEnvelope count (2 * slots)
            schurBound)
      have zeroRecursive := zeroBound.trans sourceToRecursive
      have matrixRecursive : PolynomialMatrix.Resource.Gaussian.Magnitude.MatrixWithin
          matrix recursiveBound := by
        intro row column
        exact Dense.Resource.polynomialWithin_mono Purelib.Data.Gaussian.Resource.Model.gaussianModel
          (matrixWithin row column) sourceToRecursive
      have promote : ∀ {polynomial : Dense.Gaussian.NormalizedPolynomial} {steps : Nat},
          Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel polynomial
            (Algebra.Field.Resource.Magnitude.grow Purelib.Data.Gaussian.Resource.Model.gaussianModel
              recursiveBound steps) →
          steps ≤ outputSteps →
          Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel polynomial
            outputBound := by
        intro polynomial steps within stepsLe
        exact Dense.Resource.polynomialWithin_mono Purelib.Data.Gaussian.Resource.Model.gaussianModel
          within
          (Algebra.Field.Resource.Magnitude.grow_mono_steps
            Purelib.Data.Gaussian.Resource.Model.gaussianModel recursiveBound
            stepsLe)
      change PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data.DataWithin
        (PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData (count + 1) matrix)
        outputBound
      constructor
      · dsimp only [PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData, -eq_self, -iff_self]
        have product := Dense.Resource.mul_within Purelib.Data.Gaussian.Resource.Model.gaussianModel
          zeroRecursive (matrixRecursive 0 0) smallerWithin.scalar
        exact promote product (by
          have headSlots := matrixSlots 0 0
          calc
            2 * (PolynomialMatrix.Basic.head matrix).coeffs.length ≤
                2 * slots := Nat.mul_le_mul_left 2 headSlots
            _ = 2 * slots + 0 * recursiveSlots + 0 * count + 0 := by omega0
            _ ≤ outputSteps :=
              Purelib.Data.Nat.Bounds.Linear.weighted_sum_le_eight_mul_sum slots recursiveSlots count
                2 0 0 0 (by decide) (by decide) (by decide) (by decide))
      · intro row column
        let a := PolynomialMatrix.Basic.head matrix
        let top := PolynomialMatrix.Basic.topRow matrix
        let left := PolynomialMatrix.Basic.leftColumn matrix
        let inverse := smaller.inverse
        have aWithin : Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel
            a recursiveBound := matrixRecursive 0 0
        have aSlots : a.coeffs.length ≤ slots := matrixSlots 0 0
        have topWithin : ∀ index, Dense.Resource.PolynomialWithin
            Purelib.Data.Gaussian.Resource.Model.gaussianModel (top index) recursiveBound :=
          fun index => by
            simpa only [top, PolynomialMatrix.Basic.topRow,
              Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] using
              matrixRecursive 0 index.succ
        have topSlots : ∀ index, (top index).coeffs.length ≤ slots :=
          fun index => by
            simpa only [top, PolynomialMatrix.Basic.topRow,
              Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] using
              matrixSlots 0 index.succ
        have leftWithin : ∀ index, Dense.Resource.PolynomialWithin
            Purelib.Data.Gaussian.Resource.Model.gaussianModel (left index) recursiveBound :=
          fun index => by
            simpa only [left, PolynomialMatrix.Basic.leftColumn,
              Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] using
              matrixRecursive index.succ 0
        have inverseWithin : ∀ i j, Dense.Resource.PolynomialWithin
            Purelib.Data.Gaussian.Resource.Model.gaussianModel (inverse i j)
              recursiveBound := smallerWithin.inverse
        have inverseSlots : ∀ i j,
            (inverse i j).coeffs.length ≤ recursiveSlots :=
          smallerSlotData.inverse
        have inverseColumn : ∀ index, Dense.Resource.PolynomialWithin
            Purelib.Data.Gaussian.Resource.Model.gaussianModel
              (PolynomialMatrix.Basic.matrixVector inverse left index)
              (Algebra.Field.Resource.Magnitude.grow Purelib.Data.Gaussian.Resource.Model.gaussianModel
                recursiveBound
                (2 * recursiveSlots + count)) := by
          intro index
          simpa only [PolynomialMatrix.Basic.matrixVector,
            Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] using
            Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Magnitude.dot_within (inverse index) left
              recursiveBound recursiveSlots
              zeroRecursive (fun middle => inverseWithin index middle)
              leftWithin (fun middle => inverseSlots index middle)
        have rowInverse : ∀ index, Dense.Resource.PolynomialWithin
            Purelib.Data.Gaussian.Resource.Model.gaussianModel
              (PolynomialMatrix.Basic.vectorMatrix top inverse index)
              (Algebra.Field.Resource.Magnitude.grow Purelib.Data.Gaussian.Resource.Model.gaussianModel
                recursiveBound
                (2 * slots + count)) := by
          intro index
          simpa only [PolynomialMatrix.Basic.vectorMatrix,
            Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] using
            Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Magnitude.dot_within top
              (Data.Vector.Basic.vectorOfFn fun middle =>
                inverse middle index)
              recursiveBound slots zeroRecursive topWithin
              (fun middle => by
                simpa only [Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] using
                  inverseWithin middle index)
              topSlots
        unfold PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData
          PolynomialMatrix.Inverse.Scaled.Block.blockInverse
        simp only [Matrix.matrixOfFn_apply, -eq_self, -iff_self]
        refine Data.Fin.cases_induction ?_ (fun rowIndex => ?_) row
        · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) column
          · let preSteps := 2 * recursiveSlots + count
            let preBound := Algebra.Field.Resource.Magnitude.grow
              Purelib.Data.Gaussian.Resource.Model.gaussianModel
              recursiveBound preSteps
            have topPre : ∀ index, Dense.Resource.PolynomialWithin
                Purelib.Data.Gaussian.Resource.Model.gaussianModel (top index) preBound :=
              fun index => Dense.Resource.polynomialWithin_mono
                Purelib.Data.Gaussian.Resource.Model.gaussianModel (topWithin index)
                (Algebra.Field.Resource.Magnitude.bound_le_grow
                  Purelib.Data.Gaussian.Resource.Model.gaussianModel
                  recursiveBound preSteps)
            have columnPre : ∀ index, Dense.Resource.PolynomialWithin
                Purelib.Data.Gaussian.Resource.Model.gaussianModel
                  (PolynomialMatrix.Basic.matrixVector inverse left index)
                  preBound := inverseColumn
            have inner := Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Magnitude.dot_within top
              (PolynomialMatrix.Basic.matrixVector inverse left)
              preBound slots
              (zeroRecursive.trans (Algebra.Field.Resource.Magnitude.bound_le_grow
                Purelib.Data.Gaussian.Resource.Model.gaussianModel recursiveBound preSteps))
              topPre columnPre topSlots
            have scalarPre := Dense.Resource.polynomialWithin_mono
              Purelib.Data.Gaussian.Resource.Model.gaussianModel smallerWithin.scalar
              (Algebra.Field.Resource.Magnitude.bound_le_grow
                Purelib.Data.Gaussian.Resource.Model.gaussianModel
                recursiveBound (preSteps + (2 * slots + count)))
            rw [Algebra.Field.Resource.Magnitude.grow_add] at inner
            have corner := Dense.Resource.add_within Purelib.Data.Gaussian.Resource.Model.gaussianModel
              (zeroRecursive.trans (Algebra.Field.Resource.Magnitude.bound_le_grow
                Purelib.Data.Gaussian.Resource.Model.gaussianModel recursiveBound _))
              scalarPre inner
            rw [Algebra.Field.Resource.Magnitude.grow_add] at corner
            exact promote corner (by
              dsimp only [preSteps, outputSteps, -eq_self, -iff_self]
              calc
                2 * recursiveSlots + count + (2 * slots + count) + 1 =
                    2 * slots + 2 * recursiveSlots + 2 * count + 1 := by omega0
                _ ≤ 8 * (slots + recursiveSlots + count + 1) :=
                  Purelib.Data.Nat.Bounds.Linear.weighted_sum_le_eight_mul_sum slots recursiveSlots
                    count
                    2 2 2 1 (by decide) (by decide) (by decide) (by decide))
          · let preSteps := 2 * slots + count + 1
            let preBound := Algebra.Field.Resource.Magnitude.grow
              Purelib.Data.Gaussian.Resource.Model.gaussianModel
              recursiveBound preSteps
            have oneLePre : 1 ≤ preSteps := by
              unfold preSteps
              exact Nat.succ_le_succ (Nat.zero_le (2 * slots + count))
            have negated := Dense.Resource.neg_within Purelib.Data.Gaussian.Resource.Model.gaussianModel
              aWithin
            have negPre := Dense.Resource.polynomialWithin_mono
              Purelib.Data.Gaussian.Resource.Model.gaussianModel negated
              (Algebra.Field.Resource.Magnitude.grow_mono_steps
                Purelib.Data.Gaussian.Resource.Model.gaussianModel
                recursiveBound oneLePre)
            have rowPre : Dense.Resource.PolynomialWithin
                Purelib.Data.Gaussian.Resource.Model.gaussianModel
                (PolynomialMatrix.Basic.vectorMatrix top inverse
                  columnIndex) preBound := Dense.Resource.polynomialWithin_mono
              Purelib.Data.Gaussian.Resource.Model.gaussianModel (rowInverse columnIndex)
              (Algebra.Field.Resource.Magnitude.grow_mono_steps
                Purelib.Data.Gaussian.Resource.Model.gaussianModel
                recursiveBound (show 2 * slots + count ≤ preSteps by
                  unfold preSteps
                  exact Nat.le_add_right (2 * slots + count) 1))
            have product := Dense.Resource.mul_within Purelib.Data.Gaussian.Resource.Model.gaussianModel
              (zeroRecursive.trans (Algebra.Field.Resource.Magnitude.bound_le_grow
                Purelib.Data.Gaussian.Resource.Model.gaussianModel recursiveBound preSteps))
              negPre rowPre
            rw [Algebra.Field.Resource.Magnitude.grow_add] at product
            exact promote product (by
              dsimp only [preSteps, outputSteps, -eq_self, -iff_self]
              have negSlots := Purelib.Polynomial.Dense.Gaussian.Resource.Slots.neg_slots a
              have twiceNegLe : 2 * (-a).coeffs.length ≤ 2 * slots :=
                Nat.mul_le_mul_left 2 (negSlots.trans aSlots)
              refine (Nat.add_le_add_left twiceNegLe
                (2 * slots + count + 1)).trans ?_
              calc
                2 * slots + count + 1 + 2 * slots =
                    4 * slots + 0 * recursiveSlots + 1 * count + 1 := by omega0
                _ ≤ 8 * (slots + recursiveSlots + count + 1) :=
                  Purelib.Data.Nat.Bounds.Linear.weighted_sum_le_eight_mul_sum slots recursiveSlots
                    count
                    4 0 1 1 (by decide) (by decide) (by decide) (by decide))
        · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) column
          · let preSteps := 2 * recursiveSlots + count + 1
            let preBound := Algebra.Field.Resource.Magnitude.grow
              Purelib.Data.Gaussian.Resource.Model.gaussianModel
              recursiveBound preSteps
            have oneLePre : 1 ≤ preSteps := by
              unfold preSteps
              exact Nat.succ_le_succ
                (Nat.zero_le (2 * recursiveSlots + count))
            have negated := Dense.Resource.neg_within Purelib.Data.Gaussian.Resource.Model.gaussianModel
              aWithin
            have negPre := Dense.Resource.polynomialWithin_mono
              Purelib.Data.Gaussian.Resource.Model.gaussianModel negated
              (Algebra.Field.Resource.Magnitude.grow_mono_steps
                Purelib.Data.Gaussian.Resource.Model.gaussianModel
                recursiveBound oneLePre)
            have columnPre : Dense.Resource.PolynomialWithin
                Purelib.Data.Gaussian.Resource.Model.gaussianModel
                (PolynomialMatrix.Basic.matrixVector inverse left
                  rowIndex) preBound := Dense.Resource.polynomialWithin_mono
              Purelib.Data.Gaussian.Resource.Model.gaussianModel (inverseColumn rowIndex)
              (Algebra.Field.Resource.Magnitude.grow_mono_steps
                Purelib.Data.Gaussian.Resource.Model.gaussianModel
                recursiveBound
                  (show 2 * recursiveSlots + count ≤ preSteps by
                    unfold preSteps
                    exact Nat.le_add_right
                      (2 * recursiveSlots + count) 1))
            have product := Dense.Resource.mul_within Purelib.Data.Gaussian.Resource.Model.gaussianModel
              (zeroRecursive.trans (Algebra.Field.Resource.Magnitude.bound_le_grow
                Purelib.Data.Gaussian.Resource.Model.gaussianModel recursiveBound preSteps))
              negPre columnPre
            rw [Algebra.Field.Resource.Magnitude.grow_add] at product
            exact promote product (by
              dsimp only [preSteps, outputSteps, -eq_self, -iff_self]
              have negSlots := Purelib.Polynomial.Dense.Gaussian.Resource.Slots.neg_slots a
              have twiceNegLe : 2 * (-a).coeffs.length ≤ 2 * slots :=
                Nat.mul_le_mul_left 2 (negSlots.trans aSlots)
              refine (Nat.add_le_add_left twiceNegLe
                (2 * recursiveSlots + count + 1)).trans ?_
              calc
                2 * recursiveSlots + count + 1 + 2 * slots =
                    2 * slots + 2 * recursiveSlots + 1 * count + 1 := by omega0
                _ ≤ 8 * (slots + recursiveSlots + count + 1) :=
                  Purelib.Data.Nat.Bounds.Linear.weighted_sum_le_eight_mul_sum slots recursiveSlots
                    count
                    2 2 1 1 (by decide) (by decide) (by decide) (by decide))
          · have square := Dense.Resource.mul_within
              Purelib.Data.Gaussian.Resource.Model.gaussianModel zeroRecursive aWithin aWithin
            let preSteps := 2 * slots
            let preBound := Algebra.Field.Resource.Magnitude.grow
              Purelib.Data.Gaussian.Resource.Model.gaussianModel
              recursiveBound preSteps
            have squarePre := Dense.Resource.polynomialWithin_mono
              Purelib.Data.Gaussian.Resource.Model.gaussianModel square
              (Algebra.Field.Resource.Magnitude.grow_mono_steps
                Purelib.Data.Gaussian.Resource.Model.gaussianModel
                recursiveBound (Nat.mul_le_mul_left 2 aSlots))
            have inversePre := Dense.Resource.polynomialWithin_mono
              Purelib.Data.Gaussian.Resource.Model.gaussianModel
              (inverseWithin rowIndex columnIndex)
              (Algebra.Field.Resource.Magnitude.bound_le_grow
                Purelib.Data.Gaussian.Resource.Model.gaussianModel
                recursiveBound preSteps)
            have product := Dense.Resource.mul_within Purelib.Data.Gaussian.Resource.Model.gaussianModel
              (zeroRecursive.trans (Algebra.Field.Resource.Magnitude.bound_le_grow
                Purelib.Data.Gaussian.Resource.Model.gaussianModel recursiveBound preSteps))
              squarePre inversePre
            rw [Algebra.Field.Resource.Magnitude.grow_add] at product
            exact promote product (by
              dsimp only [preSteps, outputSteps, -eq_self, -iff_self]
              have squareSlots := Purelib.Polynomial.Dense.Gaussian.Resource.Slots.mul_slots a a
              have squareLe : (a * a).coeffs.length ≤ 2 * slots :=
                calc
                  (a * a).coeffs.length ≤ a.coeffs.length + a.coeffs.length :=
                    squareSlots
                  _ ≤ slots + slots := Nat.add_le_add aSlots aSlots
                  _ = 2 * slots := by omega0
              have twiceSquareLe :
                  2 * (a * a).coeffs.length ≤ 4 * slots := by
                exact (Nat.mul_le_mul_left 2 squareLe).trans_eq (by omega0)
              refine (Nat.add_le_add_left twiceSquareLe (2 * slots)).trans ?_
              calc
                2 * slots + 4 * slots =
                    6 * slots + 0 * recursiveSlots + 0 * count + 0 := by omega0
                _ ≤ 8 * (slots + recursiveSlots + count + 1) :=
                  Purelib.Data.Nat.Bounds.Linear.weighted_sum_le_eight_mul_sum slots recursiveSlots
                    count
                    6 0 0 0 (by decide) (by decide) (by decide) (by decide))

section
/-- Increasing the shared magnitude bound preserves the retained inverse-data certificate. -/
private theorem dataWithin_mono {count : Nat}
    {data : Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic.GaussianScaledInverseData count}
    {left right : Nat}
    (resource :
      Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data.DataWithin data
      left)
    (order : left ≤ right) :
    Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data.DataWithin data
      right :=
  { scalar := Dense.Resource.polynomialWithin_mono Purelib.Data.Gaussian.Resource.Model.gaussianModel
      resource.scalar order
    inverse := fun row column =>
      Dense.Resource.polynomialWithin_mono Purelib.Data.Gaussian.Resource.Model.gaussianModel
        (resource.inverse row column) order }
end

end

end Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data
