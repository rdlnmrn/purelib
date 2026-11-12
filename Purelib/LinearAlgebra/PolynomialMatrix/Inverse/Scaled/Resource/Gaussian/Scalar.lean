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

open Purelib.Data.Gaussian.Resource
open Purelib.Algebra.Field.Resource

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
      let slots := Resource.Gaussian.Slots.matrixSlotBound matrix
      let schurBound := Magnitude.grow
        Model.gaussianModel bound (2 * slots + 2)
      let smallerBound :=
        Scalar.scaledScalarMagnitudeEnvelope
        count
        (Basic.schur matrix) schurBound
      Magnitude.grow Model.gaussianModel smallerBound
        (2 * slots)

/-- The recursive scalar magnitude envelope is at least its supplied input bound. -/
theorem scaledScalar_bound_le_envelope :
    ∀ (count : Nat) (matrix : Basic.GaussianNumberMatrix count) (bound : Nat),
      bound ≤ scaledScalarMagnitudeEnvelope count matrix bound
  | 0, _, _ => le_refl _
  | count + 1, matrix, bound => by
      dsimp only [scaledScalarMagnitudeEnvelope, -eq_self,
        -iff_self]
      exact (Magnitude.bound_le_grow
        Model.gaussianModel bound _).trans
        ((Scalar.scaledScalar_bound_le_envelope
          count
          (Basic.schur matrix)
          (Magnitude.grow Model.gaussianModel bound
            (2 * Resource.Gaussian.Slots.matrixSlotBound matrix + 2))).trans
            (Magnitude.bound_le_grow
              Model.gaussianModel _ _))

/-- The polynomial Schur complement satisfies the input magnitude bound advanced by its slot budget.

The input bound also covers zero, and the retained maximum coefficient length pays for both products and subtraction. -/
theorem schur_within {count : Nat}
    {matrix : Basic.GaussianNumberMatrix (count + 1)} {bound : Nat}
    (zeroBound : Model.gaussianModel.magnitude 0 ≤ bound)
    (bounded : Resource.Gaussian.Magnitude.MatrixWithin matrix bound) :
    Resource.Gaussian.Magnitude.MatrixWithin (Basic.schur matrix)
      (Magnitude.grow Model.gaussianModel bound (2 *
        Resource.Gaussian.Slots.matrixSlotBound matrix + 2)) := by
  intro row column
  let slots := Resource.Gaussian.Slots.matrixSlotBound matrix
  have headWithin : PolynomialWithin Model.gaussianModel
      (Basic.head matrix) bound := by
    simpa only [Basic.head, -eq_self, -iff_self] using bounded 0 0
  have tailWithin : PolynomialWithin Model.gaussianModel
      (Basic.tail matrix row column) bound := by
    simpa only [Basic.tail,
      SquareMatrix.matrixOfFn_apply, -eq_self, -iff_self] using
      bounded row.succ column.succ
  have leftWithin : PolynomialWithin Model.gaussianModel
      (Basic.leftColumn matrix row) bound := by
    simpa only [Basic.leftColumn,
      Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] using bounded row.succ 0
  have topWithin : PolynomialWithin Model.gaussianModel
      (Basic.topRow matrix column) bound := by
    simpa only [Basic.topRow,
      Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] using bounded 0 column.succ
  have first := Dense.Resource.mul_within Model.gaussianModel zeroBound
    headWithin tailWithin
  have second := Dense.Resource.mul_within Model.gaussianModel zeroBound
    leftWithin topWithin
  have headLength := Resource.Gaussian.Slots.matrixSlot_le matrix 0 0
  have leftLength :
      (Basic.leftColumn matrix row).coeffs.length ≤
        slots := by
    simpa only [Basic.leftColumn,
      Data.Vector.Basic.vectorOfFn_apply, slots, -eq_self, -iff_self] using
      Resource.Gaussian.Slots.matrixSlot_le matrix row.succ 0
  have firstBound : PolynomialWithin Model.gaussianModel
      (Basic.head matrix *
        Basic.tail matrix row column)
      (Magnitude.grow Model.gaussianModel bound (2 *
        slots)) :=
    Dense.Resource.polynomialWithin_mono Model.gaussianModel first
      (Magnitude.grow_mono_steps Model.gaussianModel
        bound (Nat.mul_le_mul_left 2 headLength))
  have secondBound : PolynomialWithin Model.gaussianModel
      (Basic.leftColumn matrix row *
        Basic.topRow matrix column)
      (Magnitude.grow Model.gaussianModel bound (2 *
        slots)) :=
    Dense.Resource.polynomialWithin_mono Model.gaussianModel second
      (Magnitude.grow_mono_steps Model.gaussianModel
        bound (Nat.mul_le_mul_left 2 leftLength))
  have difference := Dense.Resource.sub_within Model.gaussianModel
    (zeroBound.trans (Magnitude.bound_le_grow
      Model.gaussianModel bound (2 * slots)))
    firstBound secondBound
  rw [Magnitude.grow_add] at difference
  simpa only [Basic.schur,
    SquareMatrix.matrixOfFn_apply, slots, -eq_self, -iff_self] using difference

/-- The recursive inverse scalar satisfies its matrix-dependent magnitude envelope.

The supplied input bound covers every matrix coefficient as well as zero and one. -/
theorem scaledInverseScalar_within :
    ∀ (count : Nat) (matrix : Basic.GaussianNumberMatrix count) (bound : Nat),
      Model.gaussianModel.magnitude 0 ≤ bound →
      Model.gaussianModel.magnitude (1 : Data.Gaussian.Basic.Number) ≤ bound
        →
      Resource.Gaussian.Magnitude.MatrixWithin matrix bound →
      PolynomialWithin Model.gaussianModel
        (Compute.scaledInverseData count matrix).scalar
        (scaledScalarMagnitudeEnvelope count matrix bound)
  | 0, _, bound, _, oneBound, _ => by
      simpa only [Compute.scaledInverseData,
        scaledScalarMagnitudeEnvelope, -eq_self, -iff_self]
        using Dense.Resource.constant_within Model.gaussianModel oneBound
  | count + 1, matrix, bound, zeroBound, oneBound, matrixWithin => by
      let slots := Resource.Gaussian.Slots.matrixSlotBound matrix
      let schurBound := Magnitude.grow
        Model.gaussianModel bound (2 * slots + 2)
      let smallerBound := scaledScalarMagnitudeEnvelope count
        (Basic.schur matrix) schurBound
      have schurWithin := schur_within zeroBound matrixWithin
      have smallerWithin :=
        Scalar.scaledInverseScalar_within count
        (Basic.schur matrix) schurBound
        (zeroBound.trans (Magnitude.bound_le_grow
          Model.gaussianModel bound _))
        (oneBound.trans (Magnitude.bound_le_grow
          Model.gaussianModel bound _)) schurWithin
      have headWithin := Dense.Resource.polynomialWithin_mono
        Model.gaussianModel (matrixWithin 0 0)
        ((Magnitude.bound_le_grow Model.gaussianModel
          bound _).trans
          (scaledScalar_bound_le_envelope count
            (Basic.schur matrix) schurBound))
      have product := Dense.Resource.mul_within Model.gaussianModel
        (zeroBound.trans
          ((Magnitude.bound_le_grow
            Model.gaussianModel bound _).trans
            (scaledScalar_bound_le_envelope count
              (Basic.schur matrix) schurBound)))
        headWithin smallerWithin
      have headLength := Resource.Gaussian.Slots.matrixSlot_le matrix 0 0
      dsimp only [Compute.scaledInverseData, -eq_self, -iff_self]
      apply Dense.Resource.polynomialWithin_mono Model.gaussianModel product
      apply Magnitude.grow_mono_steps
        Model.gaussianModel smallerBound
      exact Nat.mul_le_mul_left 2 headLength

end

end Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Scalar
