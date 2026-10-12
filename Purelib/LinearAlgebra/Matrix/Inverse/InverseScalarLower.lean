module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Blocks
import Purelib.LinearAlgebra.Matrix.Schur

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse
import Purelib.LinearAlgebra.Matrix.Inverse.SchurActionLower
public import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.LinearAlgebra.Matrix.Inverse.ActionPivot
import Purelib.LinearAlgebra.Matrix.Inverse.InverseAggregateLower
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic

open Purelib

open Purelib.Data.Rat

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

open Purelib.Riemann

@[expose] public section

/-! An explicit positive lower bound for the actual pivot-complete inverse scalar in every finite dimension. -/
namespace Purelib.LinearAlgebra.Matrix.Inverse.InverseScalarLower

open Purelib.Data.Rat.Fraction.Compatibility

/-- The recursive bound pays the finite pivot count and both conjugate-weighted aggregations. -/
def scalarNormLower : Nat →
  Fraction.Rational → Fraction.Rational
  | 0, _ => 1
  | size + 1, lower =>
      let pivot := lower / ((size + 1 : Nat) : Fraction.Rational)
      (pivot * Purelib.LinearAlgebra.Matrix.Inverse.InverseScalarLower.scalarNormLower size (lower *
        pivot)) ^ 4

/-- The recursive scalar norm bound is positive for every positive supplied action bound. -/
theorem scalarNormLower_positive : ∀
  (size : Nat) (lower : Fraction.Rational), 0 < lower → 0 < SquareMatrix.Inverse.InverseScalarLower.scalarNormLower size
  lower
  | 0, _, _ => by
      change (0 : Fraction.Rational) < 1
      decide
  | size + 1, lower, positive => by
      have pivotPositive := Fraction.Order.Field.div_pos_direct positive (Fraction.Cast.Order.natCast_pos_direct
        (Nat.zero_lt_succ size))
      exact Fraction.Order.Arithmetic.pow_pos_direct (Fraction.Order.Arithmetic.mul_pos_direct pivotPositive
        (Purelib.LinearAlgebra.Matrix.Inverse.InverseScalarLower.scalarNormLower_positive size _
          (Fraction.Order.Arithmetic.mul_pos_direct positive pivotPositive))) 4

/-- The finite sum of coefficient squared norms is nonnegative. -/
private theorem
  coefficientNorm_nonnegative {size :
  Nat} (coefficients : Gaussian.Energy.GaussianVector size) :
    0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := open Purelib.Algebra in by
  have bound := SquareMatrix.Inverse.PivotedScaledInverse.coordinateSum_mono (fun _ : Fin size => 0) (fun index =>
    Data.Gaussian.Norm.Basic.normSq (coefficients index))
    (fun index => Data.Gaussian.Norm.Basic.normSq_nonneg (coefficients index))
  rw [FiniteSum.Fin.sumFin_zero] at bound
  have read := FiniteSum.Fin.sumFin_congr (fun index : Fin size =>
    Data.Gaussian.Norm.Basic.normSq_eq_canonical (coefficients index))
  exact bound.trans_eq read

/-- Quantitative completeness of the canonical fraction-free inverse, without a caller pivot or determinant certificate.
-/
theorem
  completeScaledInverse_norm_lower :
  ∀ {size : Nat} (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square size) (lower : Fraction.Rational),
    0 < lower →
    (∀ coefficients, lower * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      Readings.PreparedObservationCoercivity.coefficientNormSq (LinearAlgebra.Gaussian.Energy.periodCombination
      coefficients matrix)) →
    SquareMatrix.Inverse.InverseScalarLower.scalarNormLower size lower ≤ Data.Gaussian.Norm.Basic.normSq
      (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse matrix).scalar
  | 0, _, _, _, _ => by
      change (1 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (1 : Data.Gaussian.Basic.Canonical)
      decide
  | size + 1, matrix, lower, positive, coercive => by
      obtain ⟨pivot, pivotBound⟩ := SquareMatrix.Inverse.ActionPivot.exists_first_row_pivot matrix lower coercive
      let pivotFloor := lower / ((size + 1 : Nat) : Fraction.Rational)
      have pivotPositive : 0 < pivotFloor := Fraction.Order.Field.div_pos_direct positive
        (Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ size))
      let pivoted := SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix matrix 0 pivot
      have headBound : pivotFloor ≤ Data.Gaussian.Norm.Basic.normSq (SquareMatrix.Blocks.head pivoted) := by
        rw [SquareMatrix.Inverse.ActionPivot.pivotMatrix_zero_head]
        exact pivotBound
      have pivotCoercive := SquareMatrix.Inverse.ActionPivot.pivotMatrix_zero_action_lower matrix pivot lower coercive
      have smallerCoercive (coefficients : Gaussian.Energy.GaussianVector size) :
          (lower * pivotFloor) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
            Readings.PreparedObservationCoercivity.coefficientNormSq (LinearAlgebra.Gaussian.Energy.periodCombination
            coefficients (SquareMatrix.Schur.schur pivoted)) :=
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct headBound positive.le)
          (LinearAlgebra.Matrix.Inverse.InverseScalarLower.coefficientNorm_nonnegative
            coefficients)).trans
          (SquareMatrix.Inverse.SchurActionLower.schur_action_lower pivoted lower positive.le pivotCoercive
            coefficients)
      have smaller :=
        Purelib.LinearAlgebra.Matrix.Inverse.InverseScalarLower.completeScaledInverse_norm_lower
        (SquareMatrix.Schur.schur pivoted) (lower * pivotFloor)
        (Fraction.Order.Arithmetic.mul_pos_direct positive pivotPositive) smallerCoercive
      have smallerPositive := SquareMatrix.Inverse.InverseScalarLower.scalarNormLower_positive size (lower * pivotFloor)
        (Fraction.Order.Arithmetic.mul_pos_direct positive pivotPositive)
      have branchBound : pivotFloor * SquareMatrix.Inverse.InverseScalarLower.scalarNormLower size (lower * pivotFloor)
        ≤ Data.Gaussian.Norm.Basic.normSq (SquareMatrix.Inverse.PivotedScaledInverse.completeExactBranch matrix
        0 pivot).scalar :=
        ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct headBound smallerPositive.le).trans
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct smaller (Data.Gaussian.Norm.Basic.normSq_nonneg
            (SquareMatrix.Blocks.head pivoted)))).trans_eq
          (SquareMatrix.Inverse.InverseAggregateLower.completeExactBranch_norm matrix 0 pivot).symm
      exact SquareMatrix.Inverse.InverseAggregateLower.completeScaledInverse_branch_lower matrix 0 pivot _
        (Fraction.Order.Arithmetic.mul_nonneg_direct pivotPositive.le smallerPositive.le) branchBound

end Purelib.LinearAlgebra.Matrix.Inverse.InverseScalarLower
