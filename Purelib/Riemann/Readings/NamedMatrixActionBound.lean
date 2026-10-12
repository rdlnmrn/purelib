module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication

public import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Tactic.Ring

public section

/-! A cached coefficient-independent action bound for all samples of a named period matrix. -/
namespace Purelib.Riemann.Readings.NamedMatrixActionBound

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg normSq_mul)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_mul_left sumFin_mul_right sumFin_zero)
open Purelib.LinearAlgebra.Matrix (matrixOfFn matrixOfFn_apply)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Riemann.Periods.PeriodMatrix (Coordinate NamedMatrix sampledMatrix sampledMatrix_apply)
open Purelib.Algebra in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- One coefficient's squared norm is bounded by the total coefficient squared norm. -/
private theorem norm_entry_le {count : Nat} (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count) (index
  : Fin
  count) :
    Data.Gaussian.Norm.Basic.normSq (coefficients index) ≤ coefficientNormSq coefficients := by
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  change _ ≤ FiniteSum.Fin.sumFin (fun row => Gaussian.Basic.Canonical.normSq (coefficients row))
  rw [← FiniteSum.Fin.sumFin_ite_eq index (fun row => Gaussian.Basic.Canonical.normSq (coefficients row))]
  apply FiniteSum.Rational.Order.Positivity.sumFin_mono
  intro row
  by_cases same : row = index
  · rw [if_pos same]
  · rw [if_neg same]
    exact Gaussian.Basic.Canonical.normSq_nonneg _

open Purelib.Algebra in
open Purelib.Approximation in
open Purelib.LinearAlgebra in
set_option genInjectivity false in
/-- A cached bound for every sampled action of one named matrix.

The entries retain the names' center bounds; the scale is the matrix size times their sum, plus one, independently of
the stage and coefficient vector. -/
structure UniformActionBound {size : Nat} (matrix : NamedMatrix size) where
  /-- The retained matrix of named-entry center bounds. -/ entries : Purelib.LinearAlgebra.Matrix Coordinate size
  /-- Each retained entry is the exact center bound of its original named matrix entry. -/ entries_eq : ∀ row column,
    entries row column =
    (Gaussian.Name.Sampling.approximation (matrix row column).name).centerBound
  /-- The retained uniform action scale. -/ scale : Coordinate
  /-- The scale equals the matrix size times the total entry bound, plus one. -/ scale_eq : scale = (size : Coordinate)
    * FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row => entries row column)) + 1

constructive_injectivity UniformActionBound

namespace UniformActionBound

variable {size : Nat} {matrix : NamedMatrix size}

open Purelib.Algebra in
open Purelib.Approximation in
open Purelib.LinearAlgebra in
/-- Cache all named-entry bounds and their uniform action scale.

Read each original name's approximation bound and retain the exact finite sum used by the scale. -/
@[expose] def build (matrix : NamedMatrix size) : UniformActionBound matrix :=
  let entries := Matrix.matrixOfFn fun row column => (Gaussian.Name.Sampling.approximation
    (matrix row column).name).centerBound
  ⟨entries, Matrix.matrixOfFn_apply _, (size : Coordinate) * FiniteSum.Fin.sumFin (fun column
    => FiniteSum.Fin.sumFin (fun row => entries row column)) + 1, rfl⟩

variable (bound : UniformActionBound matrix)

open Purelib.Approximation in
/-- Every cached named-entry bound is nonnegative. -/
theorem entry_nonnegative (row column : Fin size) : 0 ≤ bound.entries row column := by
  rw [bound.entries_eq]
  exact (Gaussian.Name.Sampling.approximation (matrix row column).name).centerBound_nonneg

open Purelib.Data in
/-- The cached action scale is strictly positive. -/
theorem scale_positive : 0 < bound.scale := by
  rw [bound.scale_eq]
  exact Rat.Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le size))
      (Purelib.Algebra.FiniteSum.Rational.Order.weight_sum_nonnegative _ (fun column =>
        Purelib.Algebra.FiniteSum.Rational.Order.weight_sum_nonnegative _ (fun row => bound.entry_nonnegative row
        column)))) (by decide)

open Purelib.Approximation in
open Purelib.Data in
/-- Every sampled matrix entry satisfies its cached bound at every stage. -/
theorem sample_entry_bound (stage : Nat) (row column : Fin size) :
    Data.Gaussian.Norm.Basic.normSq (sampledMatrix matrix stage row column) ≤ bound.entries row column := by
  rw [bound.entries_eq, sampledMatrix_apply]
  exact (Gaussian.Name.Sampling.approximation (matrix row column).name).sample_bounded stage

open Purelib.Algebra in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Bound the squared norm of a sampled matrix action uniformly in its coefficients.

At every stage, the period-combination norm is at most the cached scale times the coefficient norm, using the same
original named matrix. -/
theorem action_bound (stage : Nat) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector size) :
    coefficientNormSq (Gaussian.Energy.periodCombination coefficients (sampledMatrix matrix stage)) ≤
      bound.scale * coefficientNormSq coefficients := by
  have columnBound (column : Fin size) :
      Data.Gaussian.Norm.Basic.normSq (Gaussian.Energy.periodCombination coefficients (sampledMatrix matrix stage)
        column) ≤
        (size : Coordinate) * (coefficientNormSq coefficients * FiniteSum.Fin.sumFin (fun row => bound.entries row
          column)) := by
    unfold Gaussian.Energy.periodCombination
    rw [Matrix.Multiplication.vectorMatrix_apply]
    have estimate := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin
      (fun row => coefficients row * sampledMatrix matrix stage row column)
      (fun row => coefficientNormSq coefficients * bound.entries row column) (fun row => by
        rw [Gaussian.Norm.Basic.normSq_mul]
        exact (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (norm_entry_le coefficients row)
          (Gaussian.Norm.Basic.normSq_nonneg _)).trans
          (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (bound.sample_entry_bound stage row column)
            (Purelib.Algebra.FiniteSum.Rational.Order.weight_sum_nonnegative _ (fun index =>
              Gaussian.Basic.Canonical.normSq_nonneg (coefficients index)))))
    rw [FiniteSum.Fin.sumFin_mul_left] at estimate
    exact estimate
  have total := FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ columnBound
  rw [FiniteSum.Fin.sumFin_mul_left, FiniteSum.Fin.sumFin_mul_left] at total
  have coefficientNonnegative : 0 ≤ coefficientNormSq coefficients :=
    Purelib.Algebra.FiniteSum.Rational.Order.weight_sum_nonnegative _ (fun index =>
      Gaussian.Basic.Canonical.normSq_nonneg (coefficients index))
  have actionNormEq : FiniteSum.Fin.sumFin
      (fun index => Data.Gaussian.Norm.Basic.normSq (Gaussian.Energy.periodCombination coefficients
        (sampledMatrix matrix stage) index)) =
      coefficientNormSq (Gaussian.Energy.periodCombination coefficients
        (sampledMatrix matrix stage)) := by
    apply FiniteSum.Fin.sumFin_congr
    intro index
    exact Gaussian.Norm.Basic.normSq_eq_canonical _
  rw [actionNormEq] at total
  apply total.trans
  rw [bound.scale_eq]
  calc
    _ = ((size : Coordinate) * FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row => bound.entries row
      column))) * coefficientNormSq coefficients := by
      ring1
    _ ≤ _ := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (le_add_of_nonneg_right (by decide))
      coefficientNonnegative

end UniformActionBound
end Purelib.Riemann.Readings.NamedMatrixActionBound
