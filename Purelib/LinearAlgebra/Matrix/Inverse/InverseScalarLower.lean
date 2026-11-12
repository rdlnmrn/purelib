module
import Purelib.LinearAlgebra.Matrix.Permutation
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

open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Gaussian.Norm

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
      (pivot * InverseScalarLower.scalarNormLower size (lower *
        pivot)) ^ 4

/-- The recursive scalar norm bound is positive for every positive supplied action bound. -/
theorem scalarNormLower_positive : ∀
  (size : Nat) (lower : Fraction.Rational), 0 < lower → 0 < scalarNormLower size
  lower
  | 0, _, _ => by
      change (0 : Fraction.Rational) < 1
      decide
  | size + 1, lower, positive => by
      have pivotPositive := Field.div_pos_direct positive (Fraction.Cast.Order.natCast_pos_direct
        (Nat.zero_lt_succ size))
      exact Arithmetic.pow_pos_direct (Arithmetic.mul_pos_direct pivotPositive
        (InverseScalarLower.scalarNormLower_positive size _
          (Arithmetic.mul_pos_direct positive pivotPositive))) 4

/-- The finite sum of coefficient squared norms is nonnegative. -/
private theorem
  coefficientNorm_nonnegative {size :
  Nat} (coefficients : Gaussian.Energy.GaussianVector size) :
    0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := open Purelib.Algebra in by
  have bound := PivotedScaledInverse.coordinateSum_mono (fun _ : Fin size => 0) (fun index =>
    Basic.normSq (coefficients index))
    (fun index => Basic.normSq_nonneg (coefficients index))
  rw [FiniteSum.Fin.sumFin_zero] at bound
  have read := FiniteSum.Fin.sumFin_congr (fun index : Fin size =>
    Basic.normSq_eq_canonical (coefficients index))
  exact bound.trans_eq read

/-- Quantitative completeness of the canonical fraction-free inverse, without a caller pivot or determinant certificate.
-/
theorem
  completeScaledInverse_norm_lower :
  ∀ {size : Nat} (matrix : PivotedScaledInverse.Square size) (lower : Fraction.Rational),
    0 < lower →
    (∀ coefficients, lower * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      Readings.PreparedObservationCoercivity.coefficientNormSq (Gaussian.Energy.periodCombination
      coefficients matrix)) →
    scalarNormLower size lower ≤ Basic.normSq
      (PivotedScaledInverse.completeScaledInverse matrix).scalar
  | 0, _, _, _, _ => by
      change (1 : Fraction.Rational) ≤ Basic.normSq (1 : Data.Gaussian.Basic.Canonical)
      decide
  | size + 1, matrix, lower, positive, coercive => by
      obtain ⟨pivot, pivotBound⟩ := ActionPivot.exists_first_row_pivot matrix lower coercive
      let pivotFloor := lower / ((size + 1 : Nat) : Fraction.Rational)
      have pivotPositive : 0 < pivotFloor := Field.div_pos_direct positive
        (Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ size))
      let pivoted := SquareMatrix.Permutation.pivotMatrix matrix 0 pivot
      have headBound : pivotFloor ≤ Basic.normSq (Blocks.head pivoted) := by
        rw [ActionPivot.pivotMatrix_zero_head]
        exact pivotBound
      have pivotCoercive := ActionPivot.pivotMatrix_zero_action_lower matrix pivot lower coercive
      have smallerCoercive (coefficients : Gaussian.Energy.GaussianVector size) :
          (lower * pivotFloor) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
            Readings.PreparedObservationCoercivity.coefficientNormSq (Gaussian.Energy.periodCombination
            coefficients (Schur.schur pivoted)) :=
        (Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Arithmetic.mul_le_mul_of_nonneg_left_direct headBound positive.le)
          (coefficientNorm_nonnegative
            coefficients)).trans
          (SchurActionLower.schur_action_lower pivoted lower positive.le pivotCoercive
            coefficients)
      have smaller :=
        InverseScalarLower.completeScaledInverse_norm_lower
        (Schur.schur pivoted) (lower * pivotFloor)
        (Arithmetic.mul_pos_direct positive pivotPositive) smallerCoercive
      have smallerPositive := scalarNormLower_positive size (lower * pivotFloor)
        (Arithmetic.mul_pos_direct positive pivotPositive)
      have branchBound : pivotFloor * scalarNormLower size (lower * pivotFloor)
        ≤ Basic.normSq (PivotedScaledInverse.completeExactBranch matrix
        0 pivot).scalar :=
        ((Arithmetic.mul_le_mul_of_nonneg_right_direct headBound smallerPositive.le).trans
          (Arithmetic.mul_le_mul_of_nonneg_left_direct smaller (Basic.normSq_nonneg
            (Blocks.head pivoted)))).trans_eq
          (InverseAggregateLower.completeExactBranch_norm matrix 0 pivot).symm
      exact InverseAggregateLower.completeScaledInverse_branch_lower matrix 0 pivot _
        (Arithmetic.mul_nonneg_direct pivotPositive.le smallerPositive.le) branchBound

end Purelib.LinearAlgebra.Matrix.Inverse.InverseScalarLower
