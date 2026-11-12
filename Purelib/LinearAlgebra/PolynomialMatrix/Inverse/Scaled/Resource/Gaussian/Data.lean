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

open Purelib.Data.Gaussian.Resource
open Purelib.Algebra.Field.Resource
open Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Magnitude

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
    PolynomialWithin Model.gaussianModel
    data.scalar bound
  /-- Every coefficient of every retained inverse entry satisfies the shared magnitude bound. -/ inverse :
    MatrixWithin data.inverse bound

/-- Compute a recursive coefficient-magnitude envelope for polynomial inverse data.

Each step pays for the Schur complement, the retained smaller slot envelope, and the block reconstruction. -/
@[expose] def dataMagnitudeEnvelope : Nat → Nat → Nat → Nat
  | 0, _, bound => bound
  | count + 1, slots, bound =>
      let schurBound := Magnitude.grow
        Model.gaussianModel bound
        (2 * slots + 2)
      let recursiveBound :=
        Data.dataMagnitudeEnvelope count (2 *
        slots) schurBound
      let recursiveSlots := Slots.dataSlotEnvelope count (2 * slots)
      Magnitude.grow Model.gaussianModel
        recursiveBound
        (8 * (slots + recursiveSlots + count + 1))

/-- The inverse-data magnitude envelope is at least its supplied input bound. -/
theorem bound_le_dataMagnitudeEnvelope : ∀ count slots bound,
    bound ≤ dataMagnitudeEnvelope count slots bound
  | 0, _, _ => le_refl _
  | count + 1, slots, bound => by
      dsimp only [dataMagnitudeEnvelope, -eq_self, -iff_self]
      exact (Magnitude.bound_le_grow
        Model.gaussianModel bound _).trans
        ((Data.bound_le_dataMagnitudeEnvelope
          count (2 * slots) _).trans
          (Magnitude.bound_le_grow
            Model.gaussianModel _ _))

/-- The computed polynomial inverse data satisfy the recursive magnitude envelope.

The input matrix has the supplied slot and coefficient bounds, and the same magnitude bound covers zero and one. -/
theorem scaledInverseData_within :
    ∀ (count : Nat) (matrix : Basic.GaussianNumberMatrix count)
      (slots bound : Nat),
      Model.gaussianModel.magnitude 0 ≤ bound →
      Model.gaussianModel.magnitude
        (1 : Data.Gaussian.Basic.Number) ≤ bound →
      Resource.Gaussian.Slots.MatrixSlotsWithin matrix slots →
      MatrixWithin matrix bound →
      DataWithin
        (Compute.scaledInverseData count matrix)
        (dataMagnitudeEnvelope count slots bound)
  | 0, _, _, bound, _, oneBound, _, _ => by
      constructor
      · simpa only [Compute.scaledInverseData,
          dataMagnitudeEnvelope, -eq_self, -iff_self] using
          Dense.Resource.constant_within Model.gaussianModel oneBound
      · intro row
        exact Fin.elim0 row
  | count + 1, matrix, slots, bound, zeroBound, oneBound, matrixSlots,
      matrixWithin => by
      let schurMatrix := Basic.schur matrix
      let schurBound := Magnitude.grow
        Model.gaussianModel bound
        (2 * slots + 2)
      have schurSlots : Resource.Gaussian.Slots.MatrixSlotsWithin schurMatrix (2 * slots) := by
        intro row column
        exact (Slots.schur_slots matrix row column).trans
          (Nat.mul_le_mul_left 2 (Resource.Gaussian.Slots.matrixSlotBound_le matrixSlots))
      have rawSchurWithin := Scalar.schur_within
        zeroBound matrixWithin
      have schurWithin : MatrixWithin
          schurMatrix schurBound := by
        intro row column
        exact Dense.Resource.polynomialWithin_mono Model.gaussianModel
          (rawSchurWithin row column)
          (Magnitude.grow_mono_steps
            Model.gaussianModel bound
            (Nat.add_le_add_right
              (Nat.mul_le_mul_left 2 (Resource.Gaussian.Slots.matrixSlotBound_le matrixSlots)) 2))
      let smaller := Compute.scaledInverseData
        count schurMatrix
      let recursiveBound := dataMagnitudeEnvelope count (2 *
        slots) schurBound
      let recursiveSlots := Slots.dataSlotEnvelope count (2 * slots)
      have smallerWithin : DataWithin smaller recursiveBound :=
        Data.scaledInverseData_within count
          schurMatrix (2 * slots) schurBound
          (zeroBound.trans
            (Magnitude.bound_le_grow
              Model.gaussianModel bound _))
          (oneBound.trans
            (Magnitude.bound_le_grow
              Model.gaussianModel bound _))
          schurSlots schurWithin
      have smallerSlotData := Slots.scaledInverseData_slots count
        schurMatrix
        (2 * slots) schurSlots
      let outputSteps := 8 * (slots + recursiveSlots + count + 1)
      let outputBound := Magnitude.grow
        Model.gaussianModel
        recursiveBound outputSteps
      have sourceToRecursive : bound ≤ recursiveBound :=
        (Magnitude.bound_le_grow Model.gaussianModel
          bound _).trans
          (bound_le_dataMagnitudeEnvelope count (2 * slots)
            schurBound)
      have zeroRecursive := zeroBound.trans sourceToRecursive
      have matrixRecursive : MatrixWithin
          matrix recursiveBound := by
        intro row column
        exact Dense.Resource.polynomialWithin_mono Model.gaussianModel
          (matrixWithin row column) sourceToRecursive
      have promote : ∀ {polynomial : Dense.Gaussian.NormalizedPolynomial} {steps : Nat},
          PolynomialWithin Model.gaussianModel polynomial
            (Magnitude.grow Model.gaussianModel
              recursiveBound steps) →
          steps ≤ outputSteps →
          PolynomialWithin Model.gaussianModel polynomial
            outputBound := by
        intro polynomial steps within stepsLe
        exact Dense.Resource.polynomialWithin_mono Model.gaussianModel
          within
          (Magnitude.grow_mono_steps
            Model.gaussianModel recursiveBound
            stepsLe)
      change DataWithin
        (Compute.scaledInverseData (count + 1) matrix)
        outputBound
      constructor
      · dsimp only [Compute.scaledInverseData, -eq_self, -iff_self]
        have product := Dense.Resource.mul_within Model.gaussianModel
          zeroRecursive (matrixRecursive 0 0) smallerWithin.scalar
        exact promote product (by
          have headSlots := matrixSlots 0 0
          calc
            2 * (Basic.head matrix).coeffs.length ≤
                2 * slots := Nat.mul_le_mul_left 2 headSlots
            _ = 2 * slots + 0 * recursiveSlots + 0 * count + 0 := by omega0
            _ ≤ outputSteps :=
              Data.Nat.Bounds.Linear.weighted_sum_le_eight_mul_sum slots recursiveSlots count
                2 0 0 0 (by decide) (by decide) (by decide) (by decide))
      · intro row column
        let a := Basic.head matrix
        let top := Basic.topRow matrix
        let left := Basic.leftColumn matrix
        let inverse := smaller.inverse
        have aWithin : PolynomialWithin Model.gaussianModel
            a recursiveBound := matrixRecursive 0 0
        have aSlots : a.coeffs.length ≤ slots := matrixSlots 0 0
        have topWithin : ∀ index, PolynomialWithin
            Model.gaussianModel (top index) recursiveBound :=
          fun index => by
            simpa only [top, Basic.topRow,
              Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] using
              matrixRecursive 0 index.succ
        have topSlots : ∀ index, (top index).coeffs.length ≤ slots :=
          fun index => by
            simpa only [top, Basic.topRow,
              Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] using
              matrixSlots 0 index.succ
        have leftWithin : ∀ index, PolynomialWithin
            Model.gaussianModel (left index) recursiveBound :=
          fun index => by
            simpa only [left, Basic.leftColumn,
              Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] using
              matrixRecursive index.succ 0
        have inverseWithin : ∀ i j, PolynomialWithin
            Model.gaussianModel (inverse i j)
              recursiveBound := smallerWithin.inverse
        have inverseSlots : ∀ i j,
            (inverse i j).coeffs.length ≤ recursiveSlots :=
          smallerSlotData.inverse
        have inverseColumn : ∀ index, PolynomialWithin
            Model.gaussianModel
              (Basic.matrixVector inverse left index)
              (Magnitude.grow Model.gaussianModel
                recursiveBound
                (2 * recursiveSlots + count)) := by
          intro index
          simpa only [Basic.matrixVector,
            Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] using
            Resource.Gaussian.Magnitude.dot_within (inverse index) left
              recursiveBound recursiveSlots
              zeroRecursive (fun middle => inverseWithin index middle)
              leftWithin (fun middle => inverseSlots index middle)
        have rowInverse : ∀ index, PolynomialWithin
            Model.gaussianModel
              (Basic.vectorMatrix top inverse index)
              (Magnitude.grow Model.gaussianModel
                recursiveBound
                (2 * slots + count)) := by
          intro index
          simpa only [Basic.vectorMatrix,
            Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] using
            Resource.Gaussian.Magnitude.dot_within top
              (Data.Vector.Basic.vectorOfFn fun middle =>
                inverse middle index)
              recursiveBound slots zeroRecursive topWithin
              (fun middle => by
                simpa only [Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] using
                  inverseWithin middle index)
              topSlots
        change PolynomialWithin Model.gaussianModel (Block.blockInverse matrix smaller row column) outputBound
        rewrite [Block.blockInverse_apply]
        refine Data.Fin.cases_induction ?_ (fun rowIndex => ?_) row
        · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) column
          · let preSteps := 2 * recursiveSlots + count
            let preBound := Magnitude.grow
              Model.gaussianModel
              recursiveBound preSteps
            have topPre : ∀ index, PolynomialWithin
                Model.gaussianModel (top index) preBound :=
              fun index => Dense.Resource.polynomialWithin_mono
                Model.gaussianModel (topWithin index)
                (Magnitude.bound_le_grow
                  Model.gaussianModel
                  recursiveBound preSteps)
            have columnPre : ∀ index, PolynomialWithin
                Model.gaussianModel
                  (Basic.matrixVector inverse left index)
                  preBound := inverseColumn
            have inner := Resource.Gaussian.Magnitude.dot_within top
              (Basic.matrixVector inverse left)
              preBound slots
              (zeroRecursive.trans (Magnitude.bound_le_grow
                Model.gaussianModel recursiveBound preSteps))
              topPre columnPre topSlots
            have scalarPre := Dense.Resource.polynomialWithin_mono
              Model.gaussianModel smallerWithin.scalar
              (Magnitude.bound_le_grow
                Model.gaussianModel
                recursiveBound (preSteps + (2 * slots + count)))
            rw [Magnitude.grow_add] at inner
            have corner := Dense.Resource.add_within Model.gaussianModel
              (zeroRecursive.trans (Magnitude.bound_le_grow
                Model.gaussianModel recursiveBound _))
              scalarPre inner
            rw [Magnitude.grow_add] at corner
            exact promote corner (by
              dsimp only [preSteps, outputSteps, -eq_self, -iff_self]
              calc
                2 * recursiveSlots + count + (2 * slots + count) + 1 =
                    2 * slots + 2 * recursiveSlots + 2 * count + 1 := by omega0
                _ ≤ 8 * (slots + recursiveSlots + count + 1) :=
                  Data.Nat.Bounds.Linear.weighted_sum_le_eight_mul_sum slots recursiveSlots
                    count
                    2 2 2 1 (by decide) (by decide) (by decide) (by decide))
          · let preSteps := 2 * slots + count + 1
            let preBound := Magnitude.grow
              Model.gaussianModel
              recursiveBound preSteps
            have oneLePre : 1 ≤ preSteps := by
              unfold preSteps
              exact Nat.succ_le_succ (Nat.zero_le (2 * slots + count))
            have negated := Dense.Resource.neg_within Model.gaussianModel
              aWithin
            have negPre := Dense.Resource.polynomialWithin_mono
              Model.gaussianModel negated
              (Magnitude.grow_mono_steps
                Model.gaussianModel
                recursiveBound oneLePre)
            have rowPre : PolynomialWithin
                Model.gaussianModel
                (Basic.vectorMatrix top inverse
                  columnIndex) preBound := Dense.Resource.polynomialWithin_mono
              Model.gaussianModel (rowInverse columnIndex)
              (Magnitude.grow_mono_steps
                Model.gaussianModel
                recursiveBound (show 2 * slots + count ≤ preSteps by
                  unfold preSteps
                  exact Nat.le_add_right (2 * slots + count) 1))
            have product := Dense.Resource.mul_within Model.gaussianModel
              (zeroRecursive.trans (Magnitude.bound_le_grow
                Model.gaussianModel recursiveBound preSteps))
              negPre rowPre
            rw [Magnitude.grow_add] at product
            exact promote product (by
              dsimp only [preSteps, outputSteps, -eq_self, -iff_self]
              have negSlots := Dense.Gaussian.Resource.Slots.neg_slots a
              have twiceNegLe : 2 * (-a).coeffs.length ≤ 2 * slots :=
                Nat.mul_le_mul_left 2 (negSlots.trans aSlots)
              refine (Nat.add_le_add_left twiceNegLe
                (2 * slots + count + 1)).trans ?_
              calc
                2 * slots + count + 1 + 2 * slots =
                    4 * slots + 0 * recursiveSlots + 1 * count + 1 := by omega0
                _ ≤ 8 * (slots + recursiveSlots + count + 1) :=
                  Data.Nat.Bounds.Linear.weighted_sum_le_eight_mul_sum slots recursiveSlots
                    count
                    4 0 1 1 (by decide) (by decide) (by decide) (by decide))
        · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) column
          · let preSteps := 2 * recursiveSlots + count + 1
            let preBound := Magnitude.grow
              Model.gaussianModel
              recursiveBound preSteps
            have oneLePre : 1 ≤ preSteps := by
              unfold preSteps
              exact Nat.succ_le_succ
                (Nat.zero_le (2 * recursiveSlots + count))
            have negated := Dense.Resource.neg_within Model.gaussianModel
              aWithin
            have negPre := Dense.Resource.polynomialWithin_mono
              Model.gaussianModel negated
              (Magnitude.grow_mono_steps
                Model.gaussianModel
                recursiveBound oneLePre)
            have columnPre : PolynomialWithin
                Model.gaussianModel
                (Basic.matrixVector inverse left
                  rowIndex) preBound := Dense.Resource.polynomialWithin_mono
              Model.gaussianModel (inverseColumn rowIndex)
              (Magnitude.grow_mono_steps
                Model.gaussianModel
                recursiveBound
                  (show 2 * recursiveSlots + count ≤ preSteps by
                    unfold preSteps
                    exact Nat.le_add_right
                      (2 * recursiveSlots + count) 1))
            have product := Dense.Resource.mul_within Model.gaussianModel
              (zeroRecursive.trans (Magnitude.bound_le_grow
                Model.gaussianModel recursiveBound preSteps))
              negPre columnPre
            rw [Magnitude.grow_add] at product
            exact promote product (by
              dsimp only [preSteps, outputSteps, -eq_self, -iff_self]
              have negSlots := Dense.Gaussian.Resource.Slots.neg_slots a
              have twiceNegLe : 2 * (-a).coeffs.length ≤ 2 * slots :=
                Nat.mul_le_mul_left 2 (negSlots.trans aSlots)
              refine (Nat.add_le_add_left twiceNegLe
                (2 * recursiveSlots + count + 1)).trans ?_
              calc
                2 * recursiveSlots + count + 1 + 2 * slots =
                    2 * slots + 2 * recursiveSlots + 1 * count + 1 := by omega0
                _ ≤ 8 * (slots + recursiveSlots + count + 1) :=
                  Data.Nat.Bounds.Linear.weighted_sum_le_eight_mul_sum slots recursiveSlots
                    count
                    2 2 1 1 (by decide) (by decide) (by decide) (by decide))
          · have square := Dense.Resource.mul_within
              Model.gaussianModel zeroRecursive aWithin aWithin
            let preSteps := 2 * slots
            let preBound := Magnitude.grow
              Model.gaussianModel
              recursiveBound preSteps
            have squarePre := Dense.Resource.polynomialWithin_mono
              Model.gaussianModel square
              (Magnitude.grow_mono_steps
                Model.gaussianModel
                recursiveBound (Nat.mul_le_mul_left 2 aSlots))
            have inversePre := Dense.Resource.polynomialWithin_mono
              Model.gaussianModel
              (inverseWithin rowIndex columnIndex)
              (Magnitude.bound_le_grow
                Model.gaussianModel
                recursiveBound preSteps)
            have product := Dense.Resource.mul_within Model.gaussianModel
              (zeroRecursive.trans (Magnitude.bound_le_grow
                Model.gaussianModel recursiveBound preSteps))
              squarePre inversePre
            rw [Magnitude.grow_add] at product
            exact promote product (by
              dsimp only [preSteps, outputSteps, -eq_self, -iff_self]
              have squareSlots := Dense.Gaussian.Resource.Slots.mul_slots a a
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
                  Data.Nat.Bounds.Linear.weighted_sum_le_eight_mul_sum slots recursiveSlots
                    count
                    6 0 0 0 (by decide) (by decide) (by decide) (by decide))

section
/-- Increasing the shared magnitude bound preserves the retained inverse-data certificate. -/
private theorem dataWithin_mono {count : Nat}
    {data : Basic.GaussianScaledInverseData count}
    {left right : Nat}
    (resource :
      DataWithin data
      left)
    (order : left ≤ right) :
    DataWithin data
      right :=
  { scalar := Dense.Resource.polynomialWithin_mono Model.gaussianModel
      resource.scalar order
    inverse := fun row column =>
      Dense.Resource.polynomialWithin_mono Model.gaussianModel
        (resource.inverse row column) order }
end

end

end Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data
