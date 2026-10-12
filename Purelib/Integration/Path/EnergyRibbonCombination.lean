module

import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

public section

/-! Coefficient-uniform energy bounds for combinations of retained ribbons.
The combined values and endpoint correction are computed from the cached
basis values. The finite trace count is retained explicitly. -/

namespace Purelib.Integration.Path.EnergyRibbonCombination

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- Bound a ribbon's corrected area difference using uniform vertex errors and centered right-path magnitudes.

The estimate keeps the original vertex count and has factor thirty-two times error times fourfold magnitude plus error.
-/
theorem difference_bound_centered {count : Nat} (ribbon : BoundaryRibbon.Ribbon count)
    {error magnitude : BoundaryRibbon.Coordinate} (errors : ∀ vertex, Data.Gaussian.Norm.Basic.normSq (ribbon.errors
      vertex)
      ≤ error)
    (centered : ∀ vertex, Data.Gaussian.Norm.Basic.normSq (ribbon.right vertex - ribbon.right 0) ≤ magnitude) :
    Data.Gaussian.Norm.Basic.normSq ribbon.difference ≤ 32 * error * (4 * magnitude + error) * (count :
      BoundaryRibbon.Coordinate) ^ 2 := by
  have errorNonnegative := (Norm.Basic.normSq_nonneg (ribbon.errors 0)).trans (errors 0)
  have increments (edge : Fin count) : Data.Gaussian.Norm.Basic.normSq (ribbon.right edge.succ - ribbon.right
    edge.castSucc)
    ≤ 4 * magnitude := by
    have estimate := (Norm.Bounds.normSq_sub_le_two (ribbon.right edge.succ - ribbon.right 0)
      (ribbon.right edge.castSucc - ribbon.right 0)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add (centered edge.succ) (centered
        edge.castSucc)) (by decide))
    rw [show (ribbon.right edge.succ - ribbon.right 0) - (ribbon.right edge.castSucc - ribbon.right 0) =
      ribbon.right edge.succ - ribbon.right edge.castSucc by ring1] at estimate
    exact estimate.trans_eq (by ring1)
  have drifts (edge : Fin count) : Data.Gaussian.Norm.Basic.normSq (ribbon.errors edge.succ - ribbon.errors
    edge.castSucc) ≤
    4 * error :=
    (Norm.Bounds.normSq_sub_le_two _ _).trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (errors edge.succ) (errors edge.castSucc)) (by decide)).trans_eq (by ring1))
  have estimate := ribbon.difference_bound (step := 1) (slope := 4 * magnitude) (drift := 4 * error) errorNonnegative
    errors
    (fun edge => (increments edge).trans_eq (by ring1)) (fun edge => (drifts edge).trans_eq (by ring1))
  exact estimate.trans_eq (by ring1)

variable {basisCount count : Nat}

section
open Purelib.Algebra
open Purelib.Data
open Purelib.Integration.Path
/-- Build the coefficient-weighted ribbon from the exact left and right vertices of each retained ribbon.

Both combined vertex vectors use the same original coefficient family and row indices; the ribbon builder caches their
area and endpoint correction. -/
@[expose] def combine (coefficients : Fin basisCount → BoundaryRibbon.Gaussian) (ribbons : Fin basisCount →
  BoundaryRibbon.Ribbon count) : BoundaryRibbon.Ribbon count :=
  BoundaryRibbon.Ribbon.build (Vector.Basic.vectorOfFn fun vertex => FiniteSum.Fin.sumFin (fun row => coefficients row *
    (ribbons row).left vertex))
    (Vector.Basic.vectorOfFn fun vertex => FiniteSum.Fin.sumFin (fun row => coefficients row * (ribbons row).right
      vertex))

/-- Read a combined left vertex as the weighted sum of the original left vertices. -/
theorem combine_left (coefficients : Fin basisCount → BoundaryRibbon.Gaussian) (ribbons : Fin basisCount →
  BoundaryRibbon.Ribbon count)
    (vertex : Fin (count + 1)) :
    (EnergyRibbonCombination.combine coefficients ribbons).left vertex = FiniteSum.Fin.sumFin (fun row => coefficients
      row * (ribbons row).left vertex) := by
  dsimp only [-eq_self, -iff_self, EnergyRibbonCombination.combine, BoundaryRibbon.Ribbon.build]
  rw [Vector.Basic.vectorOfFn_apply]

/-- Read a combined right vertex as the weighted sum of the original right vertices. -/
theorem combine_right (coefficients : Fin basisCount → BoundaryRibbon.Gaussian) (ribbons : Fin basisCount →
  BoundaryRibbon.Ribbon count)
    (vertex : Fin (count + 1)) :
    (EnergyRibbonCombination.combine coefficients ribbons).right vertex = FiniteSum.Fin.sumFin (fun row => coefficients
      row * (ribbons row).right vertex) := by
  dsimp only [-eq_self, -iff_self, EnergyRibbonCombination.combine, BoundaryRibbon.Ribbon.build]
  rw [Vector.Basic.vectorOfFn_apply]

end

section
open Purelib.Algebra
open Purelib.Integration.Path
/-- Read the combined vertex error as the weighted sum of the original ribbon errors. -/
theorem combine_errors (coefficients : Fin basisCount → BoundaryRibbon.Gaussian) (ribbons : Fin basisCount →
  BoundaryRibbon.Ribbon count)
    (vertex : Fin (count + 1)) :
    (EnergyRibbonCombination.combine coefficients ribbons).errors vertex = FiniteSum.Fin.sumFin (fun row => coefficients
      row * (ribbons row).errors vertex) := by
  rw [(EnergyRibbonCombination.combine coefficients ribbons).errors_eq, EnergyRibbonCombination.combine_left,
    EnergyRibbonCombination.combine_right, ← FiniteSum.Fin.sumFin_sub]
  apply FiniteSum.Fin.sumFin_congr
  intro row
  rw [(ribbons row).errors_eq]
  ring1

/-- The combined right path centered at its first vertex is the weighted sum of the original centered paths. -/
theorem combine_centered (coefficients : Fin basisCount → BoundaryRibbon.Gaussian) (ribbons : Fin basisCount →
  BoundaryRibbon.Ribbon count)
    (vertex : Fin (count + 1)) :
    (EnergyRibbonCombination.combine coefficients ribbons).right vertex - (EnergyRibbonCombination.combine coefficients
      ribbons).right 0 =
      FiniteSum.Fin.sumFin (fun row => coefficients row * ((ribbons row).right vertex - (ribbons row).right 0)) := by
  rw [EnergyRibbonCombination.combine_right, EnergyRibbonCombination.combine_right, ← FiniteSum.Fin.sumFin_sub]
  apply FiniteSum.Fin.sumFin_congr
  intro row
  ring1

end

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- Uniform row bounds control the weighted Gaussian sum by row count and coefficient squared-norm sum. -/
private theorem combination_bound (coefficients values : Fin basisCount → BoundaryRibbon.Gaussian) {bound :
  BoundaryRibbon.Coordinate}
    (bounded : ∀ row, Data.Gaussian.Norm.Basic.normSq (values row) ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun row => coefficients row * values row)) ≤
      (basisCount : BoundaryRibbon.Coordinate) * FiniteSum.Fin.sumFin (fun row => Data.Gaussian.Norm.Basic.normSq
        (coefficients row)) * bound := by
  have estimate := Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin
    (fun row => coefficients row * values row) (fun row => Data.Gaussian.Norm.Basic.normSq (coefficients row) * bound)
      (fun
      row => by
      rw [Norm.Basic.normSq_mul]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (bounded row) (Norm.Basic.normSq_nonneg _))
  rw [FiniteSum.Fin.sumFin_mul_right] at estimate
  exact estimate.trans_eq (by ring1)

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
/-- Bound the corrected difference of the weighted ribbon while retaining the original coefficient energy.

The common error and centered-magnitude bounds apply to every original row; the squared coefficient norm sum and squared
basis count remain outside the ribbon estimate. -/
theorem combine_difference_bound (coefficients : Fin basisCount → BoundaryRibbon.Gaussian) (ribbons : Fin basisCount →
  BoundaryRibbon.Ribbon count)
    {error magnitude : BoundaryRibbon.Coordinate} (errors : ∀ row vertex, Data.Gaussian.Norm.Basic.normSq ((ribbons
      row).errors vertex) ≤ error)
    (centered : ∀ row vertex, Data.Gaussian.Norm.Basic.normSq ((ribbons row).right vertex - (ribbons row).right 0) ≤
      magnitude) :
    Data.Gaussian.Norm.Basic.normSq (EnergyRibbonCombination.combine coefficients ribbons).difference ≤
      (basisCount : BoundaryRibbon.Coordinate) ^ 2 * (FiniteSum.Fin.sumFin (fun row => Data.Gaussian.Norm.Basic.normSq
        (coefficients row))) ^ 2 *
        (32 * error * (4 * magnitude + error) * (count : BoundaryRibbon.Coordinate) ^ 2) := by
  have combinedErrors (vertex : Fin (count + 1)) : Data.Gaussian.Norm.Basic.normSq ((EnergyRibbonCombination.combine
    coefficients ribbons).errors vertex) ≤
      (basisCount : BoundaryRibbon.Coordinate) * FiniteSum.Fin.sumFin (fun row => Data.Gaussian.Norm.Basic.normSq
        (coefficients row)) * error := by
    rw [EnergyRibbonCombination.combine_errors]
    exact EnergyRibbonCombination.combination_bound coefficients _ (fun row => errors row vertex)
  have combinedCentered (vertex : Fin (count + 1)) :
      Data.Gaussian.Norm.Basic.normSq ((EnergyRibbonCombination.combine coefficients ribbons).right vertex -
        (EnergyRibbonCombination.combine coefficients ribbons).right 0) ≤
        (basisCount : BoundaryRibbon.Coordinate) * FiniteSum.Fin.sumFin (fun row => Data.Gaussian.Norm.Basic.normSq
          (coefficients row)) * magnitude := by
    rw [EnergyRibbonCombination.combine_centered]
    exact EnergyRibbonCombination.combination_bound coefficients _ (fun row => centered row vertex)
  exact (EnergyRibbonCombination.difference_bound_centered (EnergyRibbonCombination.combine coefficients ribbons)
    combinedErrors combinedCentered).trans_eq (by ring1)

open Purelib.Integration.Path in
set_option genInjectivity false in
/-- A positive cap at most one paying the specified ribbon difference target.

The retained payment includes factor 512, the original edge count squared, and the sum of the supplied magnitude and
cap. -/
structure CombinationBudget (count : Nat) (magnitude target : BoundaryRibbon.Coordinate) where
  /-- The retained positive error cap. -/ cap : BoundaryRibbon.Coordinate
  /-- The retained cap is strictly positive. -/ positive : 0 < cap
  /-- The retained cap is at most one. -/ le_one : cap ≤ 1
  /-- The original edge count and magnitude satisfy the target payment at this cap. -/ paid : 512 * cap * (magnitude +
    cap) * (count : BoundaryRibbon.Coordinate) ^ 2 ≤ target

constructive_injectivity CombinationBudget

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- Choose a retained positive ribbon cap from the target and nonnegative magnitude.

The cap is the minimum of one and the weighted rational allowance, with an exact payment certificate for the original
edge count. -/
@[expose] def CombinationBudget.build (count : Nat) (magnitude target : BoundaryRibbon.Coordinate)
    (nonnegative : 0 ≤ magnitude) (positive : 0 < target) : EnergyRibbonCombination.CombinationBudget count magnitude
      target := by
  let weight := 512 * (magnitude + 1) * (count : BoundaryRibbon.Coordinate) ^ 2
  have weightNonnegative : 0 ≤ weight := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (add_nonneg nonnegative (by decide)))
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  let cap := min 1 (Budget.Weighted.allowance target weight)
  have capPositive : 0 < cap := Purelib.Data.Rat.Fraction.Order.Basic.lt_min (by decide)
    (Budget.Weighted.allowance_positive positive weightNonnegative)
  have capLe : cap ≤ 1 := Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _
  have paid : weight * cap ≤ target :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _)
      weightNonnegative).trans
      (Budget.Weighted.mul_allowance_le positive.le weightNonnegative)
  refine ⟨cap, capPositive, capLe, ?_⟩
  calc
    _ ≤ 512 * cap * (magnitude + 1) * (count : BoundaryRibbon.Coordinate) ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.add_le_add_direct le_rfl capLe)
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) capPositive.le))
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    _ = weight * cap := by ring1
    _ ≤ _ := paid

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- A retained cap budget bounds the weighted ribbon difference by the target times its coefficient-energy factor. -/
theorem CombinationBudget.combine_bound {magnitude target : BoundaryRibbon.Coordinate} (budget :
  EnergyRibbonCombination.CombinationBudget count magnitude target)
    (coefficients : Fin basisCount → BoundaryRibbon.Gaussian) (ribbons : Fin basisCount → BoundaryRibbon.Ribbon count)
    (errors : ∀ row vertex, Data.Gaussian.Norm.Basic.normSq ((ribbons row).errors vertex) ≤ 4 * budget.cap)
    (centered : ∀ row vertex, Data.Gaussian.Norm.Basic.normSq ((ribbons row).right vertex - (ribbons row).right 0) ≤
      magnitude) :
    Data.Gaussian.Norm.Basic.normSq (EnergyRibbonCombination.combine coefficients ribbons).difference ≤
      (basisCount : BoundaryRibbon.Coordinate) ^ 2 * (FiniteSum.Fin.sumFin (fun row => Data.Gaussian.Norm.Basic.normSq
        (coefficients row))) ^ 2 * target := by
  have estimate := EnergyRibbonCombination.combine_difference_bound coefficients ribbons errors centered
  have equal : 32 * (4 * budget.cap) * (4 * magnitude + 4 * budget.cap) * (count : BoundaryRibbon.Coordinate) ^ 2 =
      512 * budget.cap * (magnitude + budget.cap) * (count : BoundaryRibbon.Coordinate) ^ 2 := by ring1
  rw [equal] at estimate
  exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct budget.paid
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)))

end Purelib.Integration.Path.EnergyRibbonCombination
