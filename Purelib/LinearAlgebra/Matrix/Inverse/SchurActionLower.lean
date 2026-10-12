module
public import Purelib.Data.Fin
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.LinearAlgebra.Matrix.Blocks
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.LinearAlgebra.Matrix.Schur
import Purelib.LinearAlgebra.Vector.Dot

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Transport a quantitative left-action bound through the fraction-free Schur step. -/
namespace Purelib.LinearAlgebra.Matrix.Inverse.SchurActionLower

open Purelib
open Purelib.Data.Rat
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.Vector
open Purelib.Riemann

open Purelib.Data.Rat.Fraction.Compatibility

variable {size : Nat}

/-- Lift a structural coefficient vector through the fraction-free Schur step.

The leading coordinate is the negative left-column pairing; each successor coordinate multiplies the corresponding
original coefficient by the retained matrix head. -/
@[expose] def schurLift (matrix : LinearAlgebra.Gaussian.Energy.GaussianMatrix (size + 1)) (coefficients :
  Gaussian.Energy.GaussianVector size) : Gaussian.Energy.GaussianVector (size
  + 1) :=
  Data.Vector.Basic.vectorOfFn fun index => Data.Fin.cases (-(Dot.dot coefficients (SquareMatrix.Blocks.leftColumn
    matrix)))
    (fun row => SquareMatrix.Blocks.head matrix * coefficients row) index

/-- The leading coordinate of the lifted vector is the negative left-column pairing. -/
theorem schurLift_zero (matrix : LinearAlgebra.Gaussian.Energy.GaussianMatrix (size + 1)) (coefficients :
  Gaussian.Energy.GaussianVector size) :
    SquareMatrix.Inverse.SchurActionLower.schurLift matrix coefficients 0 = -(Dot.dot coefficients
      (SquareMatrix.Blocks.leftColumn matrix)) := by
  rw [SquareMatrix.Inverse.SchurActionLower.schurLift, Data.Vector.Basic.vectorOfFn_apply]
  rfl

/-- Each remaining lifted coordinate is the original coefficient multiplied by the leading matrix entry. -/
theorem schurLift_succ (matrix : LinearAlgebra.Gaussian.Energy.GaussianMatrix (size + 1)) (coefficients :
  Gaussian.Energy.GaussianVector size) (row : Fin size) :
    SquareMatrix.Inverse.SchurActionLower.schurLift matrix coefficients row.succ = SquareMatrix.Blocks.head matrix *
      coefficients row := by
  rw [SquareMatrix.Inverse.SchurActionLower.schurLift, Data.Vector.Basic.vectorOfFn_apply]
  rfl

/-- The lifted row-vector action vanishes at the leading column. -/
theorem schurLift_action_zero (matrix : LinearAlgebra.Gaussian.Energy.GaussianMatrix (size + 1)) (coefficients :
  Gaussian.Energy.GaussianVector size) :
    LinearAlgebra.Gaussian.Energy.periodCombination (SquareMatrix.Inverse.SchurActionLower.schurLift matrix
      coefficients) matrix 0 = 0 := open Purelib.Algebra in by
  unfold LinearAlgebra.Gaussian.Energy.periodCombination
  rw [SquareMatrix.Multiplication.vectorMatrix_apply, FiniteSum.Fin.sumFin_succ,
    SquareMatrix.Inverse.SchurActionLower.schurLift_zero]
  have read : FiniteSum.Fin.sumFin (fun row : Fin size => SquareMatrix.Inverse.SchurActionLower.schurLift matrix
    coefficients row.succ * matrix row.succ 0) =
      SquareMatrix.Blocks.head matrix * Dot.dot coefficients (SquareMatrix.Blocks.leftColumn matrix) := by
    apply (FiniteSum.Fin.sumFin_congr (fun row => ?_)).trans (FiniteSum.Fin.sumFin_mul_left _ _)
    rw [SquareMatrix.Inverse.SchurActionLower.schurLift_succ, SquareMatrix.Blocks.leftColumn_apply]
    ring1
  rw [read]
  change -Dot.dot coefficients (SquareMatrix.Blocks.leftColumn matrix) * SquareMatrix.Blocks.head matrix + _ = 0
  ring1

/-- The remaining lifted action coordinates equal the action on the fraction-free Schur complement. -/
theorem schurLift_action_succ (matrix : LinearAlgebra.Gaussian.Energy.GaussianMatrix (size + 1)) (coefficients :
  Gaussian.Energy.GaussianVector size) (column : Fin size) :
    LinearAlgebra.Gaussian.Energy.periodCombination (SquareMatrix.Inverse.SchurActionLower.schurLift matrix
      coefficients) matrix column.succ = LinearAlgebra.Gaussian.Energy.periodCombination coefficients
      (SquareMatrix.Schur.schur matrix) column := open Purelib.Algebra in by
  unfold LinearAlgebra.Gaussian.Energy.periodCombination
  rw [SquareMatrix.Multiplication.vectorMatrix_apply, FiniteSum.Fin.sumFin_succ,
    SquareMatrix.Inverse.SchurActionLower.schurLift_zero]
  have read : FiniteSum.Fin.sumFin (fun row : Fin size => SquareMatrix.Inverse.SchurActionLower.schurLift matrix
    coefficients row.succ * matrix row.succ column.succ) =
      SquareMatrix.Blocks.head matrix * SquareMatrix.Multiplication.vectorMatrix coefficients (SquareMatrix.Blocks.tail
        matrix) column := by
    rw [SquareMatrix.Multiplication.vectorMatrix_apply, ← FiniteSum.Fin.sumFin_mul_left]
    apply FiniteSum.Fin.sumFin_congr
    intro row
    rw [SquareMatrix.Inverse.SchurActionLower.schurLift_succ, SquareMatrix.Blocks.tail_apply]
    ring1
  rw [read, SquareMatrix.Schur.vectorMatrix_schur]
  rw [SquareMatrix.Blocks.topRow_apply]
  ring1

/-- The lifted coefficient norm is at least the pivot norm times the original coefficient norm. -/
theorem schurLift_norm_lower (matrix : LinearAlgebra.Gaussian.Energy.GaussianMatrix (size + 1)) (coefficients :
  Gaussian.Energy.GaussianVector size) :
    Data.Gaussian.Norm.Basic.normSq (SquareMatrix.Blocks.head matrix) *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      Readings.PreparedObservationCoercivity.coefficientNormSq (SquareMatrix.Inverse.SchurActionLower.schurLift matrix
      coefficients) := open Purelib.Algebra in by
  unfold Readings.PreparedObservationCoercivity.coefficientNormSq
  rw [FiniteSum.Fin.sumFin_succ, SquareMatrix.Inverse.SchurActionLower.schurLift_zero]
  have read : FiniteSum.Fin.sumFin (fun row : Fin size => Data.Gaussian.Basic.Canonical.normSq
    (SquareMatrix.Inverse.SchurActionLower.schurLift matrix coefficients row.succ)) =
      Data.Gaussian.Norm.Basic.normSq (SquareMatrix.Blocks.head matrix) * FiniteSum.Fin.sumFin (fun row =>
        Data.Gaussian.Basic.Canonical.normSq (coefficients row)) := by
    apply (FiniteSum.Fin.sumFin_congr (fun row => ?_)).trans (FiniteSum.Fin.sumFin_mul_left _ _)
    calc
      Data.Gaussian.Basic.Canonical.normSq (SquareMatrix.Inverse.SchurActionLower.schurLift matrix coefficients
        row.succ) =
          Data.Gaussian.Norm.Basic.normSq (SquareMatrix.Inverse.SchurActionLower.schurLift matrix coefficients
            row.succ) :=
        (Data.Gaussian.Norm.Basic.normSq_eq_canonical _).symm
      _ = Data.Gaussian.Norm.Basic.normSq (SquareMatrix.Blocks.head matrix) *
        Data.Gaussian.Norm.Basic.normSq (coefficients row) := by
        rw [SquareMatrix.Inverse.SchurActionLower.schurLift_succ, Data.Gaussian.Norm.Basic.normSq_mul]
      _ = Data.Gaussian.Norm.Basic.normSq (SquareMatrix.Blocks.head matrix) *
        Data.Gaussian.Basic.Canonical.normSq (coefficients row) :=
        congrArg (fun value : Fraction.Rational => Data.Gaussian.Norm.Basic.normSq (SquareMatrix.Blocks.head
          matrix) * value)
          (Data.Gaussian.Norm.Basic.normSq_eq_canonical (coefficients row))
  rw [read]
  apply le_add_of_nonneg_left
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  exact Data.Gaussian.Norm.Basic.normSq_nonneg _

/-- The lifted matrix-action norm equals the original coefficient action norm on the Schur complement. -/
theorem schurLift_action_norm (matrix : LinearAlgebra.Gaussian.Energy.GaussianMatrix (size + 1)) (coefficients :
  Gaussian.Energy.GaussianVector size) :
    Readings.PreparedObservationCoercivity.coefficientNormSq (LinearAlgebra.Gaussian.Energy.periodCombination
      (SquareMatrix.Inverse.SchurActionLower.schurLift matrix coefficients) matrix) =
      Readings.PreparedObservationCoercivity.coefficientNormSq (LinearAlgebra.Gaussian.Energy.periodCombination
        coefficients (SquareMatrix.Schur.schur matrix)) := open Purelib.Algebra in by
  unfold Readings.PreparedObservationCoercivity.coefficientNormSq
  rw [FiniteSum.Fin.sumFin_succ, SquareMatrix.Inverse.SchurActionLower.schurLift_action_zero]
  change 0 + _ = _
  rw [Fraction.Field.zero_add]
  exact FiniteSum.Fin.sumFin_congr (fun row => congrArg Data.Gaussian.Basic.Canonical.normSq
    (SquareMatrix.Inverse.SchurActionLower.schurLift_action_succ matrix coefficients row))

/-- Transfer an action lower bound to the fraction-free Schur complement.

The resulting coefficient bound is multiplied by the leading pivot squared norm; nonnegativity of the supplied lower
bound is retained. -/
theorem schur_action_lower (matrix : LinearAlgebra.Gaussian.Energy.GaussianMatrix (size + 1)) (lower :
  Fraction.Rational) (nonnegative : 0 ≤ lower)
    (coercive : ∀ coefficients, lower * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      Readings.PreparedObservationCoercivity.coefficientNormSq (LinearAlgebra.Gaussian.Energy.periodCombination
      coefficients matrix))
    (coefficients : Gaussian.Energy.GaussianVector size) :
    (lower * Data.Gaussian.Norm.Basic.normSq (SquareMatrix.Blocks.head matrix)) *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      Readings.PreparedObservationCoercivity.coefficientNormSq (LinearAlgebra.Gaussian.Energy.periodCombination
        coefficients (SquareMatrix.Schur.schur matrix)) := by
  have lifted := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (SquareMatrix.Inverse.SchurActionLower.schurLift_norm_lower matrix coefficients) nonnegative).trans
    (coercive (SquareMatrix.Inverse.SchurActionLower.schurLift matrix coefficients))
  rw [SquareMatrix.Inverse.SchurActionLower.schurLift_action_norm] at lifted
  exact (Eq.le (by ring1)).trans lifted

end Purelib.LinearAlgebra.Matrix.Inverse.SchurActionLower
