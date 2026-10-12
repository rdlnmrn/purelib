module
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Blocks
import Purelib.LinearAlgebra.Matrix.Multiplication

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse
public import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.LinearAlgebra.Matrix.Inverse.SchurActionLower
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

/-! A quantitatively nonzero pivot from a finite action lower bound, with column-pivot invariance. -/
namespace Purelib.LinearAlgebra.Matrix.Inverse.ActionPivot

open Purelib.Algebra
open Purelib
open Purelib.Data.Rat
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.Riemann

open Purelib.Data.Rat.Fraction.Compatibility

/-- Find an entry meeting a rational threshold or certify the strict finite-sum bound.

The list of coordinates is nonempty, and decidable comparisons produce the displayed disjunction. -/
private theorem entry_or_sum_lt (threshold : Fraction.Rational) : ∀ {count : Nat} (values : Fin (count + 1) →
  Fraction.Rational),
    (∃ index, threshold ≤ values index) ∨ FiniteSum.Fin.sumFin values < ((count + 1 : Nat) : Fraction.Rational) *
      threshold := by
  intro count
  induction count with
  | zero =>
      intro values
      by_cases large : threshold ≤ values 0
      · exact .inl ⟨0, large⟩
      · apply Or.inr
        rw [FiniteSum.Fin.sumFin_succ]
        change values 0 + 0 < 1 * threshold
        rw [add_zero, Fraction.Field.one_mul]
        exact lt_of_not_ge large
  | succ count ih =>
      intro values
      by_cases large : threshold ≤ values 0
      · exact .inl ⟨0, large⟩
      · rcases ih (fun index => values index.succ) with ⟨index, found⟩ | small
        · exact .inl ⟨index.succ, found⟩
        · apply Or.inr
          rw [FiniteSum.Fin.sumFin_succ]
          apply (Fraction.Order.Arithmetic.add_lt_add_direct (lt_of_not_ge large) small).trans_eq
          simp only [Purelib.Algebra.NatCast.add, Nat.cast_one]
          ring1

/-- A lower bound on a nonempty finite sum yields an entry at least that bound divided by the count. -/
theorem exists_entry_ge_mean {count : Nat} (values : Fin (count + 1) → Fraction.Rational) (lower : Fraction.Rational)
    (bounded : lower ≤ FiniteSum.Fin.sumFin values) : ∃ index, lower / ((count + 1 : Nat) : Fraction.Rational) ≤ values
      index := by
  rcases LinearAlgebra.Matrix.Inverse.ActionPivot.entry_or_sum_lt (lower / ((count + 1 : Nat) :
    Fraction.Rational)) values with found | small
  · exact found
  · have positive := Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ count)
    have read : ((count + 1 : Nat) : Fraction.Rational) * (lower / ((count + 1 : Nat) : Fraction.Rational)) = lower :=
      (Fraction.Field.mul_comm _ _).trans (Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne')
    rw [read] at small
    exact (not_lt_of_ge bounded small).elim

/-- An action lower bound bounds the squared norm of the first matrix row.

The estimate is obtained by evaluating the supplied coefficient inequality on the first coordinate unit. -/
theorem first_row_norm_lower {size : Nat} (matrix : LinearAlgebra.Gaussian.Energy.GaussianMatrix (size + 1)) (lower :
  Fraction.Rational)
    (coercive : ∀ coefficients, lower * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      Readings.PreparedObservationCoercivity.coefficientNormSq (LinearAlgebra.Gaussian.Energy.periodCombination
      coefficients matrix)) :
    lower ≤ FiniteSum.Fin.sumFin (fun column => Data.Gaussian.Norm.Basic.normSq (matrix 0 column)) := by
  let unit : Gaussian.Energy.GaussianVector (size + 1) := .cons 1 (Data.Vector.Basic.vectorOfFn fun
    _ => 0)
  have norm : Readings.PreparedObservationCoercivity.coefficientNormSq unit = 1 := by
    unfold Readings.PreparedObservationCoercivity.coefficientNormSq
    rw [FiniteSum.Fin.sumFin_succ]
    change Data.Gaussian.Basic.Canonical.normSq 1 + FiniteSum.Fin.sumFin (fun index : Fin size =>
      Data.Gaussian.Basic.Canonical.normSq (Data.Vector.Basic.vectorOfFn (fun _ : Fin size => (0 :
      Data.Gaussian.Basic.Canonical)) index)) = 1
    have zero : FiniteSum.Fin.sumFin (fun index : Fin size => Data.Gaussian.Basic.Canonical.normSq
      (Data.Vector.Basic.vectorOfFn (fun _ : Fin size => (0 : Data.Gaussian.Basic.Canonical)) index)) = 0 := by
      apply (FiniteSum.Fin.sumFin_congr (fun index => ?_)).trans FiniteSum.Fin.sumFin_zero
      rw [Data.Vector.Basic.vectorOfFn_apply]
      rfl
    rw [zero]
    decide
  have read (column : Fin (size + 1)) : LinearAlgebra.Gaussian.Energy.periodCombination unit matrix column = matrix 0
    column := by
    unfold LinearAlgebra.Gaussian.Energy.periodCombination
    rw [SquareMatrix.Multiplication.vectorMatrix_apply, FiniteSum.Fin.sumFin_succ]
    change 1 * matrix 0 column + FiniteSum.Fin.sumFin (fun index : Fin size => Data.Vector.Basic.vectorOfFn (fun _ : Fin
      size => (0 : Data.Gaussian.Basic.Canonical)) index * matrix index.succ column) = _
    have zero : FiniteSum.Fin.sumFin (fun index : Fin size => Data.Vector.Basic.vectorOfFn (fun _ : Fin size => (0 :
      Data.Gaussian.Basic.Canonical)) index * matrix index.succ column) = 0 := by
      apply (FiniteSum.Fin.sumFin_congr (fun index => ?_)).trans FiniteSum.Fin.sumFin_zero
      rw [Data.Vector.Basic.vectorOfFn_apply, zero_mul]
    rw [zero, Data.Gaussian.Basic.one_mul, Data.Gaussian.Basic.add_zero]
  have bound := coercive unit
  rw [norm, mul_one] at bound
  exact bound.trans_eq (FiniteSum.Fin.sumFin_congr (fun column =>
    (congrArg Data.Gaussian.Basic.Canonical.normSq (read column)).trans
      (Data.Gaussian.Norm.Basic.normSq_eq_canonical (matrix 0 column)).symm))

/-- An action lower bound yields a first-row entry with a quantitative squared-norm bound.

The bound is divided by the exact positive matrix dimension. -/
theorem exists_first_row_pivot {size : Nat} (matrix : LinearAlgebra.Gaussian.Energy.GaussianMatrix (size + 1)) (lower :
  Fraction.Rational)
    (coercive : ∀ coefficients, lower * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      Readings.PreparedObservationCoercivity.coefficientNormSq (LinearAlgebra.Gaussian.Energy.periodCombination
      coefficients matrix)) :
    ∃ column, lower / ((size + 1 : Nat) : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (matrix 0
      column) :=
  SquareMatrix.Inverse.ActionPivot.exists_entry_ge_mean _ _ (SquareMatrix.Inverse.ActionPivot.first_row_norm_lower
    matrix lower coercive)

/-- Swapping matrix columns permutes the coordinates of its row-vector action. -/
theorem swapColumns_action {size : Nat} (matrix : LinearAlgebra.Gaussian.Energy.GaussianMatrix (size + 1)) (pivot : Fin
  (size + 1))
    (coefficients : Gaussian.Energy.GaussianVector (size + 1)) (column : Fin (size + 1)) :
    LinearAlgebra.Gaussian.Energy.periodCombination coefficients (SquareMatrix.Inverse.PivotedScaledInverse.swapColumns
      matrix pivot) column = LinearAlgebra.Gaussian.Energy.periodCombination coefficients matrix
      (SquareMatrix.Inverse.PivotedScaledInverse.swapZero pivot column) := by
  unfold LinearAlgebra.Gaussian.Energy.periodCombination
  rw [SquareMatrix.Multiplication.vectorMatrix_apply, SquareMatrix.Multiplication.vectorMatrix_apply]
  exact FiniteSum.Fin.sumFin_congr (fun row => congrArg (fun value : Data.Gaussian.Basic.Canonical => coefficients row *
    value)
    (SquareMatrix.Inverse.PivotedScaledInverse.swapColumns_apply matrix pivot row column))

/-- A column pivot preserves the squared norm of every row-vector action. -/
theorem swapColumns_action_norm {size : Nat} (matrix : LinearAlgebra.Gaussian.Energy.GaussianMatrix (size + 1)) (pivot :
  Fin (size + 1))
    (coefficients : Gaussian.Energy.GaussianVector (size + 1)) :
    Readings.PreparedObservationCoercivity.coefficientNormSq (LinearAlgebra.Gaussian.Energy.periodCombination
      coefficients (SquareMatrix.Inverse.PivotedScaledInverse.swapColumns matrix pivot)) =
      Readings.PreparedObservationCoercivity.coefficientNormSq (LinearAlgebra.Gaussian.Energy.periodCombination
      coefficients matrix) := by
  apply (FiniteSum.Fin.sumFin_congr (fun column => congrArg Data.Gaussian.Basic.Canonical.normSq
    (SquareMatrix.Inverse.ActionPivot.swapColumns_action matrix pivot coefficients column))).trans
    (SquareMatrix.Inverse.PivotedScaledInverse.sumFin_swapZero pivot (fun column => Data.Gaussian.Basic.Canonical.normSq
      (LinearAlgebra.Gaussian.Energy.periodCombination coefficients matrix column)))

/-- A pivot using the first row only swaps the selected column with the first column. -/
theorem pivotMatrix_zero {size : Nat} (matrix : LinearAlgebra.Gaussian.Energy.GaussianMatrix (size + 1)) (pivot : Fin
  (size + 1)) :
    SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix matrix 0 pivot =
      SquareMatrix.Inverse.PivotedScaledInverse.swapColumns matrix pivot := by
  apply SquareMatrix.matrix_ext
  intro row column
  unfold SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix
  rw [SquareMatrix.Inverse.PivotedScaledInverse.swapColumns_apply,
    SquareMatrix.Inverse.PivotedScaledInverse.swapRows_apply,
    SquareMatrix.Inverse.PivotedScaledInverse.swapColumns_apply]
  have fixed : SquareMatrix.Inverse.PivotedScaledInverse.swapZero 0 row = row := by
    by_cases zero : row = 0
    · cases zero
      rfl
    · rw [SquareMatrix.Inverse.PivotedScaledInverse.swapZero, if_neg zero, if_neg zero]
  rw [fixed]

/-- Read the leading entry after pivoting a selected first-row column. -/
theorem pivotMatrix_zero_head {size : Nat} (matrix : LinearAlgebra.Gaussian.Energy.GaussianMatrix (size + 1)) (pivot :
  Fin (size + 1)) :
    SquareMatrix.Blocks.head (SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix matrix 0 pivot) = matrix 0 pivot :=
      by
  rw [SquareMatrix.Inverse.ActionPivot.pivotMatrix_zero]
  change SquareMatrix.Inverse.PivotedScaledInverse.swapColumns matrix pivot 0 0 = _
  rw [SquareMatrix.Inverse.PivotedScaledInverse.swapColumns_apply,
    SquareMatrix.Inverse.PivotedScaledInverse.swapZero_zero]

/-- A first-row column pivot preserves the supplied action lower bound. -/
theorem pivotMatrix_zero_action_lower {size : Nat} (matrix : LinearAlgebra.Gaussian.Energy.GaussianMatrix (size + 1))
  (pivot : Fin (size + 1)) (lower : Fraction.Rational)
    (coercive : ∀ coefficients, lower * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      Readings.PreparedObservationCoercivity.coefficientNormSq (LinearAlgebra.Gaussian.Energy.periodCombination
      coefficients matrix))
    (coefficients : Gaussian.Energy.GaussianVector (size + 1)) :
    lower * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      Readings.PreparedObservationCoercivity.coefficientNormSq (LinearAlgebra.Gaussian.Energy.periodCombination
      coefficients (SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix matrix 0 pivot)) := by
  rw [SquareMatrix.Inverse.ActionPivot.pivotMatrix_zero, SquareMatrix.Inverse.ActionPivot.swapColumns_action_norm]
  exact coercive coefficients

end Purelib.LinearAlgebra.Matrix.Inverse.ActionPivot
