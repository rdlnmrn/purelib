module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Integration.Path.WeightedPathComparison
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-! Retained owner errors are paid on the full centered path, including
nonzero increments at zero geometric displacement. -/
namespace Purelib.Integration.Path.OwnedPathComparison

open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)

open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Periods in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- Quarter-tolerance vertex errors bound the discrepancy of any two original path increments by the full tolerance.

Both coordinates retain the same original start and finish indices and their individual error witnesses. -/
theorem increment_difference {count : Nat} {first second : Fin (count + 1) → Stokes.PrimitivePoint}
    {tolerance : CenteredBilinearPath.Coordinate} (accurate : ∀ vertex, (PrimitiveAreaBounds.PrimitivePoint.Bounded
      ((Stokes.PrimitivePoint.sub (first vertex)) (second vertex))) (tolerance / 4))
    (start finish : Fin (count + 1)) :
    (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub ((Stokes.PrimitivePoint.sub (first finish))
      (first start))) ((Stokes.PrimitivePoint.sub (second finish)) (second start)))) tolerance := by
  have scalar {a b c d : Basic.Canonical} (last : Basic.Canonical.normSq (a - c) ≤ tolerance / 4) (initial :
    Basic.Canonical.normSq (b - d) ≤ tolerance / 4) :
      Basic.Canonical.normSq ((a - b) - (c - d)) ≤ tolerance := by
    rw [show (a - b) - (c - d) = (a - c) - (b - d) by ring1]
    have estimate := Norm.Bounds.normSq_sub_le_two (a - c) (b - d)
    rw [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical] at estimate
    exact estimate.trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct last
        initial) (by decide)).trans_eq
        ((show 2 * (tolerance / 4 + tolerance / 4) = (tolerance / 4) * 4 by ring1).trans
          (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))))
  exact ⟨scalar (accurate finish).1 (accurate start).1, scalar (accurate finish).2 (accurate start).2⟩

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Periods in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- Compare the centered areas of an owned reading and the original fixed sample under a retained noise budget.

Quarter-tolerance vertex accuracy transports the fixed sample's increment bounds to the owned sample; the estimate keeps
original total length, allowance and density. -/
theorem LengthErrorBudget.reading_comparison {count : Nat} {allowance : CenteredBilinearPath.Coordinate}
    (budget : NoisyPathArea.LengthErrorBudget count allowance)
    {first second : Fin (count + 1) → Stokes.PrimitivePoint} (owned : CenteredBilinearPath.Sample first) (fixed :
      CenteredBilinearPath.Sample second)
    (lengths : Fin count → CenteredBilinearPath.Coordinate) {density : CenteredBilinearPath.Coordinate}
    (densityNonnegative : 0 ≤ density) (nonnegative : ∀ edge, 0 ≤ lengths edge)
    (accurate : ∀ vertex, (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub (first vertex))
      (second vertex))) (budget.tolerance / 4))
    (increments : ∀ edge : Fin count, (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub (second
      edge.succ)) (second edge.castSucc))) (density * (lengths edge)^2)) :
    Data.Gaussian.Norm.Basic.normSq (owned.centeredArea - fixed.centeredArea) ≤
      40 * budget.tolerance * (4 * density + 3) * (FiniteSum.Fin.sumFin lengths + allowance)^2 := by
  have stepNonnegative (edge : Fin count) : 0 ≤ density * (lengths edge)^2 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct densityNonnegative (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  apply WeightedPathComparison.LengthErrorBudget.centered_full_comparison budget owned fixed lengths
    budget.tolerance_positive.le densityNonnegative nonnegative
  · intro vertex
    rw [owned.centered_eq, fixed.centered_eq]
    exact OwnedPathComparison.increment_difference accurate 0 vertex
  · intro edge
    have errors := OwnedPathComparison.increment_difference accurate edge.castSucc edge.succ
    have scalar {a b : Basic.Canonical} (error : Basic.Canonical.normSq (a - b) ≤ budget.tolerance)
        (bounded : Basic.Canonical.normSq b ≤ density * (lengths edge)^2) :
        Basic.Canonical.normSq a ≤ 3 * budget.tolerance + 4 * density * (lengths edge)^2 := by
      have estimate := Norm.Bounds.normSq_add_le_two (a - b) b
      rw [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical,
        sub_add_cancel] at estimate
      have lower := estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct error bounded) (by decide))
      exact lower.trans ((le_add_of_nonneg_right
        (add_nonneg budget.tolerance_positive.le (Fraction.Order.Arithmetic.mul_nonneg_direct (by
            decide : (0 : CenteredBilinearPath.Coordinate) ≤ 2) (stepNonnegative edge)))).trans_eq (by ring1))
    exact ⟨scalar errors.1 (increments edge).1, scalar errors.2 (increments edge).2⟩
  · intro edge
    have upper : density * (lengths edge)^2 ≤ 3 * budget.tolerance + 4 * density * (lengths edge)^2 :=
      (le_add_of_nonneg_right (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by
          decide : (0 : CenteredBilinearPath.Coordinate) ≤ 3) budget.tolerance_positive.le)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : CenteredBilinearPath.Coordinate) ≤ 3)
          (stepNonnegative edge)))).trans_eq (by ring1)
    exact ⟨(increments edge).1.trans upper, (increments edge).2.trans upper⟩

end Purelib.Integration.Path.OwnedPathComparison
