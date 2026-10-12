module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.NoisyPathArea
import Purelib.Integration.Path.WeightedPathComparison
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Integration.Path.OwnedPathComparison
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-! Pay owner changes without losing homogeneous coefficient dependence. -/
namespace Purelib.Integration.Path.HomogeneousOwnedPathComparison

open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)

open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Periods in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- Compare owned and fixed centered areas while retaining the common nonnegative mass factor.

The vertex and increment bounds are linear in the original mass, so the resulting area-error estimate keeps its square
outside the original length-budget bound. -/
theorem LengthErrorBudget.homogeneous_reading_comparison {count : Nat} {allowance mass :
  CenteredBilinearPath.Coordinate}
    (budget : NoisyPathArea.LengthErrorBudget count allowance) (massNonnegative : 0 ≤ mass)
    {first second : Fin (count + 1) → Stokes.PrimitivePoint} (owned : CenteredBilinearPath.Sample first) (fixed :
      CenteredBilinearPath.Sample second)
    (lengths : Fin count → CenteredBilinearPath.Coordinate) {density : CenteredBilinearPath.Coordinate}
    (densityNonnegative : 0 ≤ density) (nonnegative : ∀ edge, 0 ≤ lengths edge)
    (accurate : ∀ vertex, (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub (first vertex))
      (second vertex))) ((budget.tolerance / 4) * mass))
    (increments : ∀ edge : Fin count, (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub (second
      edge.succ)) (second edge.castSucc)))
      (density * mass * (lengths edge)^2)) :
    Data.Gaussian.Norm.Basic.normSq (owned.centeredArea - fixed.centeredArea) ≤
      40 * budget.tolerance * (4 * density + 3) * mass^2 * (FiniteSum.Fin.sumFin lengths + allowance)^2 := by
  have errors (start finish : Fin (count + 1)) :
      (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub ((Stokes.PrimitivePoint.sub (first
        finish)) (first start))) ((Stokes.PrimitivePoint.sub (second finish)) (second start)))) (budget.tolerance *
        mass) :=
    OwnedPathComparison.increment_difference (fun vertex => by
      have equal : (budget.tolerance / 4) * mass = (budget.tolerance * mass) / 4 := by
        simp only [Fraction.Field.div_eq_mul_inv_direct]
        ring1
      rw [← equal]
      exact accurate vertex) start finish
  have upper (edge : Fin count) :
      (3 * budget.tolerance + 4 * density * (lengths edge)^2) * mass ≤
        ((4 * density + 3) * mass) * (lengths edge + budget.padding)^2 :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (budget.increment_bound densityNonnegative (nonnegative
      edge)) massNonnegative).trans_eq (by ring1)
  have fixedUpper (edge : Fin count) : density * mass * (lengths edge)^2 ≤
      ((4 * density + 3) * mass) * (lengths edge + budget.padding)^2 := by
    have extra := Fraction.Order.Arithmetic.mul_nonneg_direct
      (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : CenteredBilinearPath.Coordinate) ≤ 3)
        budget.tolerance_positive.le)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 :
          CenteredBilinearPath.Coordinate) ≤ 3) densityNonnegative) (Fraction.Order.Arithmetic.sq_nonneg_direct (lengths
          edge)))) massNonnegative
    exact ((le_add_of_nonneg_right extra).trans_eq (by ring1)).trans (upper edge)
  have ownedUpper (edge : Fin count) {a b : Basic.Canonical}
      (error : Basic.Canonical.normSq (a - b) ≤ budget.tolerance * mass)
      (bounded : Basic.Canonical.normSq b ≤ density * mass * (lengths edge)^2) :
      Basic.Canonical.normSq a ≤ ((4 * density + 3) * mass) * (lengths edge + budget.padding)^2 := by
    have triangle := Norm.Bounds.normSq_add_le_two (a - b) b
    rw [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical] at triangle
    have estimate := triangle.trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct error
        bounded) (by decide : (0 : CenteredBilinearPath.Coordinate) ≤ 2))
    rw [sub_add_cancel] at estimate
    have extra := Fraction.Order.Arithmetic.mul_nonneg_direct
      (add_nonneg budget.tolerance_positive.le
        (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 :
          CenteredBilinearPath.Coordinate) ≤ 2) densityNonnegative) (Fraction.Order.Arithmetic.sq_nonneg_direct (lengths
          edge)))) massNonnegative
    exact estimate.trans (((le_add_of_nonneg_right extra).trans_eq (by ring1)).trans (upper edge))
  have weightsNonnegative (edge : Fin count) : 0 ≤ lengths edge + budget.padding :=
    add_nonneg (nonnegative edge) budget.padding_positive.le
  have bounded := WeightedPathComparison.Sample.weighted_full_comparison owned fixed (fun edge => lengths edge +
    budget.padding)
    weightsNonnegative (fun vertex => by
      rw [owned.centered_eq, fixed.centered_eq]
      exact errors 0 vertex)
    (fun edge => ⟨ownedUpper edge (errors edge.castSucc edge.succ).1 (increments edge).1,
      ownedUpper edge (errors edge.castSucc edge.succ).2 (increments edge).2⟩)
    (fun edge => ⟨(increments edge).1.trans (fixedUpper edge), (increments edge).2.trans (fixedUpper edge)⟩)
  have sumNonnegative {n : Nat} (values : Fin n → CenteredBilinearPath.Coordinate) (positive : ∀ i, 0 ≤ values i) :
      0 ≤ FiniteSum.Fin.sumFin values := by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
        rw [FiniteSum.Fin.sumFin_succ]
        exact add_nonneg (positive 0) (ih _ (fun i => positive i.succ))
  have scaleNonnegative : 0 ≤ 40 * (budget.tolerance * mass) * ((4 * density + 3) * mass) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide +kernel : (0 : CenteredBilinearPath.Coordinate) ≤ 40)
      (Fraction.Order.Arithmetic.mul_nonneg_direct budget.tolerance_positive.le massNonnegative))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by
          decide : (0 : CenteredBilinearPath.Coordinate) ≤ 4) densityNonnegative)
        (by decide : (0 : CenteredBilinearPath.Coordinate) ≤ 3)) massNonnegative)
  exact bounded.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.pow_le_pow_direct (sumNonnegative _ weightsNonnegative) (budget.total_weight_le lengths)
      2) scaleNonnegative).trans_eq (by ring1))

end Purelib.Integration.Path.HomogeneousOwnedPathComparison
