module
import Purelib.LinearAlgebra.Matrix.Permutation
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.LinearAlgebra.Matrix.Blocks
import Purelib.LinearAlgebra.Matrix.Schur

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Norm

open Purelib.Algebra

open Purelib

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

@[expose] public section

/-! Quantitative retention of a successful pivot branch in the canonical conjugate-weighted inverse. -/
namespace Purelib.LinearAlgebra.Matrix.Inverse.InverseAggregateLower

open Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse

open Purelib.Data.Rat.Fraction.Compatibility

variable {count size : Nat} {matrix : Square size}
  (branches : Fin count → ScaledInverse matrix)

/-- The conjugate-weighted aggregate scalar has real part equal to the sum of branch squared norms. -/
theorem aggregateConjugate_real :
    (PivotedScaledInverse.aggregateScaledInverse branches (fun index =>
      Data.Gaussian.Basic.conj (branches index).scalar)).scalar.re =
      FiniteSum.Fin.sumFin (fun index => Basic.normSq (branches index).scalar) := by
  rw [PivotedScaledInverse.aggregateScaledInverse_scalar,
    PivotedScaledInverse.sumFin_re]
  exact FiniteSum.Fin.sumFin_congr (fun index => PivotedScaledInverse.conj_mul_self_re (branches
    index).scalar)

/-- Each branch squared norm is bounded by the real part of the conjugate-weighted aggregate scalar. -/
theorem
  aggregateConjugate_entry_le_real
  (selected : Fin count) :
    Basic.normSq (branches selected).scalar ≤
      (PivotedScaledInverse.aggregateScaledInverse branches (fun index =>
        Data.Gaussian.Basic.conj (branches index).scalar)).scalar.re := by
  rw [aggregateConjugate_real, ← FiniteSum.Fin.sumFin_ite_eq selected (fun
    index => Basic.normSq (branches index).scalar)]
  apply PivotedScaledInverse.coordinateSum_mono
  intro index
  by_cases same : index = selected
  · rw [if_pos same]
  · rw [if_neg same]
    exact Basic.normSq_nonneg _

/-- A nonnegative lower bound for one branch norm yields its square as a lower bound for the aggregate norm. -/
theorem
  aggregateConjugate_norm_lower
  (selected : Fin count) (lower : Coordinate) (nonnegative : 0 ≤ lower)
    (bounded : lower ≤ Basic.normSq (branches selected).scalar) :
    lower ^ 2 ≤ Basic.normSq
      (PivotedScaledInverse.aggregateScaledInverse branches (fun index =>
      Data.Gaussian.Basic.conj (branches index).scalar)).scalar := open Purelib.Data.Rat in by
  have realBound := bounded.trans (aggregateConjugate_entry_le_real branches
    selected)
  have realNonnegative := nonnegative.trans realBound
  have squared := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct realBound nonnegative).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct realBound realNonnegative)
  apply (Eq.le (pow_two lower)).trans (squared.trans ?_)
  unfold Basic.normSq
  rw [pow_two]
  exact le_add_of_nonneg_right (Fraction.Order.Arithmetic.sq_nonneg_direct _)

/-- The norm of one exact pivot branch is the product of the pivot and smaller-inverse norms. -/
theorem completeExactBranch_norm
  {size : Nat} (matrix : Square (size + 1)) (row column : Fin (size + 1)) :
    Basic.normSq (PivotedScaledInverse.completeExactBranch matrix row
      column).scalar =
      Basic.normSq (Blocks.head
        (SquareMatrix.Permutation.pivotMatrix matrix row column)) *
        Basic.normSq (PivotedScaledInverse.completeScaledInverse
          (Schur.schur (SquareMatrix.Permutation.pivotMatrix matrix row column))).scalar
          := by
  change Basic.normSq (_ * _) = _
  exact Basic.normSq_mul _ _

/-- A nonnegative branch norm bound contributes its fourth power to the complete inverse norm.

The two powers arise from the nested conjugate-weighted column and row aggregations. -/
theorem
  completeScaledInverse_branch_lower
  {size : Nat} (matrix : Square (size + 1)) (row column : Fin (size + 1))
    (lower : Coordinate) (nonnegative : 0 ≤ lower) (bounded : lower ≤
      Basic.normSq (PivotedScaledInverse.completeExactBranch matrix row
      column).scalar) :
    lower ^ 4 ≤ Basic.normSq
      (PivotedScaledInverse.completeScaledInverse matrix).scalar := open Purelib.Data.Rat in by
  have inner : lower ^ 2 ≤ Basic.normSq
    (PivotedScaledInverse.completeExactRow matrix row).scalar :=
    aggregateConjugate_norm_lower
      (PivotedScaledInverse.completeExactBranch matrix row) column lower nonnegative bounded
  have outer := aggregateConjugate_norm_lower
    (PivotedScaledInverse.completeExactRow matrix) row (lower ^ 2)
    (Fraction.Order.Arithmetic.sq_nonneg_direct lower) inner
  apply (Eq.le (by ring1)).trans outer

end Purelib.LinearAlgebra.Matrix.Inverse.InverseAggregateLower
