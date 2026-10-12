module

import Purelib.Algebra.Field.Resource.Magnitude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Resource.Model
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Basic
public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Compute
public import Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Magnitude
public import Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Slots
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Resource
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Fin
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Multiplication
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Field
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Block
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Multiplication

/-!
# Retained polynomial inverse resource envelopes

The original Schur and block recurrences retain their scalar, inverse and coefficient
data. Slot and magnitude certificates bound those same stored polynomials.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Scalar

open Purelib
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra
open Purelib.Polynomial

open Purelib.Polynomial.Dense.Resource

public section

/-- Compute a coefficient-magnitude envelope for the retained recursive inverse scalar.

The recurrence follows the actual Schur matrices and their finite maximum coefficient lengths. -/
@[expose] def scaledScalarMagnitudeEnvelope :
    (count : Nat) → Basic.GaussianNumberMatrix count → Nat → Nat
  | 0, _, bound => bound
  | count + 1, matrix, bound =>
      let slots := PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound matrix
      let schurBound := Algebra.Field.Resource.Magnitude.grow
        Purelib.Data.Gaussian.Resource.Model.gaussianModel bound (2 * slots + 2)
      let smallerBound :=
        Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Scalar.scaledScalarMagnitudeEnvelope
        count
        (PolynomialMatrix.Basic.schur matrix) schurBound
      Algebra.Field.Resource.Magnitude.grow Purelib.Data.Gaussian.Resource.Model.gaussianModel smallerBound
        (2 * slots)

/-- The recursive scalar magnitude envelope is at least its supplied input bound. -/
theorem scaledScalar_bound_le_envelope :
    ∀ (count : Nat) (matrix : Basic.GaussianNumberMatrix count) (bound : Nat),
      bound ≤ PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Scalar.scaledScalarMagnitudeEnvelope count matrix bound
  | 0, _, _ => le_refl _
  | count + 1, matrix, bound => by
      dsimp only [PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Scalar.scaledScalarMagnitudeEnvelope, -eq_self,
        -iff_self]
      exact (Algebra.Field.Resource.Magnitude.bound_le_grow
        Purelib.Data.Gaussian.Resource.Model.gaussianModel bound _).trans
        ((Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Scalar.scaledScalar_bound_le_envelope
          count
          (PolynomialMatrix.Basic.schur matrix)
          (Algebra.Field.Resource.Magnitude.grow Purelib.Data.Gaussian.Resource.Model.gaussianModel bound
            (2 * PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound matrix + 2))).trans
            (Algebra.Field.Resource.Magnitude.bound_le_grow
              Purelib.Data.Gaussian.Resource.Model.gaussianModel _ _))

/-- The polynomial Schur complement satisfies the input magnitude bound advanced by its slot budget.

The input bound also covers zero, and the retained maximum coefficient length pays for both products and subtraction. -/
theorem schur_within {count : Nat}
    {matrix : Basic.GaussianNumberMatrix (count + 1)} {bound : Nat}
    (zeroBound : Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude 0 ≤ bound)
    (bounded : PolynomialMatrix.Resource.Gaussian.Magnitude.MatrixWithin matrix bound) :
    PolynomialMatrix.Resource.Gaussian.Magnitude.MatrixWithin (PolynomialMatrix.Basic.schur matrix)
      (Algebra.Field.Resource.Magnitude.grow Purelib.Data.Gaussian.Resource.Model.gaussianModel bound (2 *
        PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound matrix + 2)) := by
  intro row column
  let slots := PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound matrix
  have headWithin : Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel
      (PolynomialMatrix.Basic.head matrix) bound := by
    simpa only [PolynomialMatrix.Basic.head, -eq_self, -iff_self] using bounded 0 0
  have tailWithin : Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel
      (PolynomialMatrix.Basic.tail matrix row column) bound := by
    simpa only [PolynomialMatrix.Basic.tail,
      SquareMatrix.matrixOfFn_apply, -eq_self, -iff_self] using
      bounded row.succ column.succ
  have leftWithin : Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel
      (PolynomialMatrix.Basic.leftColumn matrix row) bound := by
    simpa only [PolynomialMatrix.Basic.leftColumn,
      Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] using bounded row.succ 0
  have topWithin : Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel
      (PolynomialMatrix.Basic.topRow matrix column) bound := by
    simpa only [PolynomialMatrix.Basic.topRow,
      Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] using bounded 0 column.succ
  have first := Dense.Resource.mul_within Purelib.Data.Gaussian.Resource.Model.gaussianModel zeroBound
    headWithin tailWithin
  have second := Dense.Resource.mul_within Purelib.Data.Gaussian.Resource.Model.gaussianModel zeroBound
    leftWithin topWithin
  have headLength := PolynomialMatrix.Resource.Gaussian.Slots.matrixSlot_le matrix 0 0
  have leftLength :
      (PolynomialMatrix.Basic.leftColumn matrix row).coeffs.length ≤
        slots := by
    simpa only [PolynomialMatrix.Basic.leftColumn,
      Data.Vector.Basic.vectorOfFn_apply, slots, -eq_self, -iff_self] using
      PolynomialMatrix.Resource.Gaussian.Slots.matrixSlot_le matrix row.succ 0
  have firstBound : Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel
      (PolynomialMatrix.Basic.head matrix *
        PolynomialMatrix.Basic.tail matrix row column)
      (Algebra.Field.Resource.Magnitude.grow Purelib.Data.Gaussian.Resource.Model.gaussianModel bound (2 *
        slots)) :=
    Dense.Resource.polynomialWithin_mono Purelib.Data.Gaussian.Resource.Model.gaussianModel first
      (Algebra.Field.Resource.Magnitude.grow_mono_steps Purelib.Data.Gaussian.Resource.Model.gaussianModel
        bound (Nat.mul_le_mul_left 2 headLength))
  have secondBound : Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel
      (PolynomialMatrix.Basic.leftColumn matrix row *
        PolynomialMatrix.Basic.topRow matrix column)
      (Algebra.Field.Resource.Magnitude.grow Purelib.Data.Gaussian.Resource.Model.gaussianModel bound (2 *
        slots)) :=
    Dense.Resource.polynomialWithin_mono Purelib.Data.Gaussian.Resource.Model.gaussianModel second
      (Algebra.Field.Resource.Magnitude.grow_mono_steps Purelib.Data.Gaussian.Resource.Model.gaussianModel
        bound (Nat.mul_le_mul_left 2 leftLength))
  have difference := Dense.Resource.sub_within Purelib.Data.Gaussian.Resource.Model.gaussianModel
    (zeroBound.trans (Algebra.Field.Resource.Magnitude.bound_le_grow
      Purelib.Data.Gaussian.Resource.Model.gaussianModel bound (2 * slots)))
    firstBound secondBound
  rw [Algebra.Field.Resource.Magnitude.grow_add] at difference
  simpa only [PolynomialMatrix.Basic.schur,
    SquareMatrix.matrixOfFn_apply, slots, -eq_self, -iff_self] using difference

/-- The recursive inverse scalar satisfies its matrix-dependent magnitude envelope.

The supplied input bound covers every matrix coefficient as well as zero and one. -/
theorem scaledInverseScalar_within :
    ∀ (count : Nat) (matrix : Basic.GaussianNumberMatrix count) (bound : Nat),
      Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude 0 ≤ bound →
      Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude (1 : Data.Gaussian.Basic.Number) ≤ bound
        →
      PolynomialMatrix.Resource.Gaussian.Magnitude.MatrixWithin matrix bound →
      Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel
        (PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData count matrix).scalar
        (PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Scalar.scaledScalarMagnitudeEnvelope count matrix bound)
  | 0, _, bound, _, oneBound, _ => by
      simpa only [PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData,
        PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Scalar.scaledScalarMagnitudeEnvelope, -eq_self, -iff_self]
        using Dense.Resource.constant_within Purelib.Data.Gaussian.Resource.Model.gaussianModel oneBound
  | count + 1, matrix, bound, zeroBound, oneBound, matrixWithin => by
      let slots := PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound matrix
      let schurBound := Algebra.Field.Resource.Magnitude.grow
        Purelib.Data.Gaussian.Resource.Model.gaussianModel bound (2 * slots + 2)
      let smallerBound := PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Scalar.scaledScalarMagnitudeEnvelope count
        (PolynomialMatrix.Basic.schur matrix) schurBound
      have schurWithin := PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Scalar.schur_within zeroBound matrixWithin
      have smallerWithin :=
        Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Scalar.scaledInverseScalar_within count
        (PolynomialMatrix.Basic.schur matrix) schurBound
        (zeroBound.trans (Algebra.Field.Resource.Magnitude.bound_le_grow
          Purelib.Data.Gaussian.Resource.Model.gaussianModel bound _))
        (oneBound.trans (Algebra.Field.Resource.Magnitude.bound_le_grow
          Purelib.Data.Gaussian.Resource.Model.gaussianModel bound _)) schurWithin
      have headWithin := Dense.Resource.polynomialWithin_mono
        Purelib.Data.Gaussian.Resource.Model.gaussianModel (matrixWithin 0 0)
        ((Algebra.Field.Resource.Magnitude.bound_le_grow Purelib.Data.Gaussian.Resource.Model.gaussianModel
          bound _).trans
          (PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Scalar.scaledScalar_bound_le_envelope count
            (PolynomialMatrix.Basic.schur matrix) schurBound))
      have product := Dense.Resource.mul_within Purelib.Data.Gaussian.Resource.Model.gaussianModel
        (zeroBound.trans
          ((Algebra.Field.Resource.Magnitude.bound_le_grow
            Purelib.Data.Gaussian.Resource.Model.gaussianModel bound _).trans
            (PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Scalar.scaledScalar_bound_le_envelope count
              (PolynomialMatrix.Basic.schur matrix) schurBound)))
        headWithin smallerWithin
      have headLength := PolynomialMatrix.Resource.Gaussian.Slots.matrixSlot_le matrix 0 0
      dsimp only [PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData, -eq_self, -iff_self]
      apply Dense.Resource.polynomialWithin_mono Purelib.Data.Gaussian.Resource.Model.gaussianModel product
      apply Algebra.Field.Resource.Magnitude.grow_mono_steps
        Purelib.Data.Gaussian.Resource.Model.gaussianModel smallerBound
      exact Nat.mul_le_mul_left 2 headLength

end

end Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Scalar
