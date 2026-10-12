module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
public import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Word.Pairing
public import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Topology.Surface.Cut.WordErrors
public import Purelib.Data.Vector.Dependent
import Init.Data.Int.Basic
import Init.Prelude
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Approximation.Rational.Budget

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Riemann.Periods

open Purelib.Riemann.Periods.WeightedPeriods

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Word

@[expose] public section

/-!
# Cached coefficient amplification for an entire finite row bank

One positive component tolerance pays every row, including empty and zero
rows. Exact coefficient caches can be reused from the actual period rows;
the allocation never assumes that the change of basis has unit norm.
-/

namespace Purelib.Approximation.Budget.WeightedRowBudgets

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_zero sumFin_ite_eq)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Periods.WeightedPeriods (Coordinate Coefficients)

/-- A finite sum of pointwise nonnegative rational coordinates is nonnegative. -/
private theorem sum_nonnegative {count : Nat} (values : Fin count → WeightedPeriods.Coordinate)
    (nonnegative : ∀ index, 0 ≤ values index) : 0 ≤ FiniteSum.Fin.sumFin values := by
  have estimate := Order.Positivity.sumFin_mono (fun _ => 0) values nonnegative
  simpa only [FiniteSum.Fin.sumFin_zero] using estimate

/-- Every entry of a nonnegative finite rational family is at most its sum. -/
private theorem term_le_sum {count : Nat} (values : Fin count → WeightedPeriods.Coordinate)
    (nonnegative : ∀ index, 0 ≤ values index) (index : Fin count) : values index ≤ FiniteSum.Fin.sumFin values := by
  have estimate := Order.Positivity.sumFin_mono (fun next => if next = index then values next else 0) values (by
    intro next
    by_cases same : next = index
    · rw [if_pos same]
    · rw [if_neg same]; exact nonnegative next)
  simpa only [FiniteSum.Fin.sumFin_ite_eq] using estimate

/-- A retained coefficient row scales a uniform primitive-point bound by its cached coefficient mass. -/
theorem Coefficients.point_bounded {count : Nat} {weights : Data.Vector Int count} (coefficients :
  WeightedPeriods.Coefficients weights)
    (values : Fin count → Stokes.PrimitivePoint) {bound : WeightedPeriods.Coordinate} (bounded : ∀ index,
      PrimitivePoint.Bounded (values index) bound) :
    PrimitivePoint.Bounded (Pairing.linear weights values) (coefficients.mass * bound) := by
  constructor
  · have estimate := coefficients.normSq_combine_le (fun index => (values index).left) (fun _ => bound)
      (fun index => (bounded index).1)
    rw [coefficients.combine_eq, coefficients.charge_constant] at estimate
    exact estimate
  · have estimate := coefficients.normSq_combine_le (fun index => (values index).right) (fun _ => bound)
      (fun index => (bounded index).2)
    rw [coefficients.combine_eq, coefficients.charge_constant] at estimate
    exact estimate

set_option genInjectivity false in
/-- A bank of retained coefficient rows with exact cached masses and total amplification.

Each row remains indexed by its original weight vector; cached masses and their finite total are certified against those
exact coefficient records. -/
structure CoefficientRows {count rows : Nat} (weights : Data.Vector (Data.Vector Int count)
  rows) where
  /-- The original dependent coefficient records for each retained weight row. -/ coefficients :
    Data.Vector.DependentVector (fun row => WeightedPeriods.Coefficients (weights row))
  /-- The cached rational mass of every coefficient row. -/ masses : Data.Vector WeightedPeriods.Coordinate
    rows
  /-- Each cached row mass equals the mass of its original coefficient record. -/ masses_eq : ∀ row, masses row =
    (coefficients.get row).mass
  /-- The cached total mass of all coefficient rows. -/ total : WeightedPeriods.Coordinate
  /-- The cached total equals the finite sum of the retained row masses. -/ total_eq : total = FiniteSum.Fin.sumFin
    masses

constructive_injectivity CoefficientRows

namespace CoefficientRows

variable {count rows : Nat} {weights : Data.Vector (Data.Vector Int count)
  rows}

/-- Cache the masses and finite total of an existing dependent bank of coefficient records.

The constructor retains those exact records and computes each row mass once. -/
def ofCoefficients (coefficients : Data.Vector.DependentVector (fun row => WeightedPeriods.Coefficients (weights row)))
  : Approximation.Budget.WeightedRowBudgets.CoefficientRows weights :=
  let masses := Data.Vector.Basic.vectorOfFn fun row => (coefficients.get row).mass
  ⟨coefficients, masses, Data.Vector.Basic.vectorOfFn_apply _, FiniteSum.Fin.sumFin masses, rfl⟩

/-- Build coefficient records for the supplied finite weight rows and cache their total mass. -/
def build (weights : Data.Vector (Data.Vector Int count) rows) :
  Approximation.Budget.WeightedRowBudgets.CoefficientRows weights :=
  Approximation.Budget.WeightedRowBudgets.CoefficientRows.ofCoefficients (DependentVector.ofFn fun row =>
    Coefficients.build (weights row))

/-- The retained total coefficient mass is nonnegative. -/
theorem total_nonnegative (bank : Approximation.Budget.WeightedRowBudgets.CoefficientRows weights) : 0 ≤ bank.total :=
  by
  rw [bank.total_eq]
  exact Approximation.Budget.WeightedRowBudgets.sum_nonnegative _ (fun row => by
      rw [bank.masses_eq];
      exact (bank.coefficients.get row).mass_nonnegative)

/-- Each original row's mass is at most the retained total coefficient mass. -/
theorem mass_le_total (bank : Approximation.Budget.WeightedRowBudgets.CoefficientRows weights) (row : Fin rows) :
  (bank.coefficients.get row).mass ≤ bank.total := by
  rw [bank.total_eq, ← bank.masses_eq]
  exact Approximation.Budget.WeightedRowBudgets.term_le_sum _ (fun row => by
      rw [bank.masses_eq];
      exact (bank.coefficients.get row).mass_nonnegative) row

/-- Allocate one common component tolerance using the retained total row mass.

The incremented denominator also covers empty banks and rows with zero amplification. -/
def perComponent (bank : Approximation.Budget.WeightedRowBudgets.CoefficientRows weights) (target :
  WeightedPeriods.Coordinate) : Fraction.Rational :=
  Weighted.allowance target bank.total

/-- A positive target gives a positive common component tolerance. -/
theorem perComponent_positive (bank : Approximation.Budget.WeightedRowBudgets.CoefficientRows weights) {target :
  WeightedPeriods.Coordinate} (positive : 0 < target) :
    0 < bank.perComponent target := Weighted.allowance_positive positive bank.total_nonnegative

/-- The total coefficient amplification times the allocated tolerance is strictly below the positive target. -/
theorem total_mul_perComponent_lt (bank : Approximation.Budget.WeightedRowBudgets.CoefficientRows weights) {target :
  WeightedPeriods.Coordinate} (positive : 0 < target) :
    bank.total * bank.perComponent target < target := by
  have extra := Fraction.Order.Arithmetic.add_lt_add_right_direct (by decide : (0 : WeightedPeriods.Coordinate) < 1)
    bank.total
  rw [zero_add, add_comm 1] at extra
  have denominatorPositive := bank.total_nonnegative.trans_lt extra
  have paid : (bank.total + 1) * bank.perComponent target = target := by
    rw [Approximation.Budget.WeightedRowBudgets.CoefficientRows.perComponent, Weighted.allowance,
      Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne'
  exact (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct extra
    (bank.perComponent_positive positive)).trans_eq paid

/-- The common component tolerance pays both primitive components of every retained coefficient row. -/
theorem point_accurate (bank : Approximation.Budget.WeightedRowBudgets.CoefficientRows weights) (values : Fin count →
  Stokes.PrimitivePoint)
    {target : WeightedPeriods.Coordinate} (positive : 0 < target) (bounded : ∀ index, PrimitivePoint.Bounded (values
      index) (bank.perComponent target))
    (row : Fin rows) :
    Data.Gaussian.Norm.Basic.normSq (Pairing.linear (weights row) values).left < target ∧
      Data.Gaussian.Norm.Basic.normSq (Pairing.linear (weights row) values).right < target := by
  have estimate := Approximation.Budget.WeightedRowBudgets.Coefficients.point_bounded (bank.coefficients.get row) values
    bounded
  have paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (bank.mass_le_total row)
    (bank.perComponent_positive positive).le).trans_lt (bank.total_mul_perComponent_lt positive)
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical,
    Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  exact ⟨estimate.1.trans_lt paid, estimate.2.trans_lt paid⟩

end CoefficientRows
end Purelib.Approximation.Budget.WeightedRowBudgets
