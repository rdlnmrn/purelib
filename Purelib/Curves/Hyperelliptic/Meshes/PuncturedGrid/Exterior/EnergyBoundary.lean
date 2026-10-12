module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartClosure
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyBoundaryControl
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartEnergy
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Tactic.Ring

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

@[expose] public section

/-!
# The odd exterior energy has no unpaid boundary term

The existing parent and closing requests pay the complete sum of shifted
potential jumps. Both the actual closed polygon and the original source
area therefore compare directly with the retained signed cap energy.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyBoundary

open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {totalTarget areaTarget target :
    Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
  {entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Entry regular lifted differential totalTarget
    areaTarget minimum}
  {charts : Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts.ChartRequest entry.request target}
  {index : Nat} {box : Rational.Box} {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}
  {plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartClosure.ChartPlan entry charts sample} {depth readingIndex :
    Nat}

/-- A nonnegative rational quarter is at most the original value. -/
private theorem quarter_le {value : Normalization.InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ value) : value /
  4 ≤ value := by
  apply (Fraction.Order.Field.div_le_iff_pos (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 4)).mpr
  exact (show value = value * 1 by ring1).trans_le
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide) nonnegative)

/-- The original parent-count-squared charge of the allocated chart tolerance fits the supplied target. -/
private theorem parent_paid :
    ((entry.prepared.program.cache.parents.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 + 1) *
      charts.parentTarget ≤ target := by
  let n : Coordinate := (entry.prepared.program.cache.parents.length : Normalization.InverseRootPolynomial.Coordinate)
  have nonnegative : 0 ≤ n := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  have denominatorPositive : 0 < 2 * (n + 1) ^ 2 := Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (Fraction.Order.Arithmetic.pow_pos_direct (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct nonnegative (by
      decide)) 2)
  have targetNonnegative : 0 ≤ charts.parentTarget := by
    rw [charts.parentTarget_eq]
    exact (Rational.Budget.Aggregate.perTerm_positive charts.positive _).le
  have coefficient : n ^ 2 + 1 ≤ 2 * (n + 1) ^ 2 := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    exact (add_nonneg (add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct n)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤
        4) nonnegative)) (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 1)).trans_eq (by ring1)
  have paid : (2 * (n + 1) ^ 2) * charts.parentTarget = target := by
    rw [charts.parentTarget_eq, Rational.Budget.Aggregate.perTerm, Rational.Budget.Aggregate.countCoordinate_eq,
      Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne'
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct coefficient targetNonnegative).trans_eq paid

/-- Expand the original parent and closing boundary charges, cancelling the final quarter exactly. -/
private theorem boundary_scale (n localTarget joining totalTarget : Normalization.InverseRootPolynomial.Coordinate) :
    2 * (n ^ 2 * (80 * localTarget + 2 * joining) + (80 * localTarget + 2 * (totalTarget / 4))) =
      160 * ((n ^ 2 + 1) * localTarget) + 4 * n ^ 2 * joining + totalTarget := by
  have cancel : 4 * (totalTarget / 4) = totalTarget := by
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  calc
    _ = 160 * ((n ^ 2 + 1) * localTarget) + 4 * n ^ 2 * joining + 4 * (totalTarget / 4) := by ring1
    _ = _ := by rw [cancel]

variable (evaluated : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartClosure.ChartPlan.Evaluation plan depth
  readingIndex) {energyTarget : Normalization.InverseRootPolynomial.Coordinate} {energyFloor : Nat}
  (energy : Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy.RequestedEnergy evaluated.chart energyTarget
    energyFloor)
  (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) (small : totalTarget ≤ 1)

include branch small in
/-- The complete original odd-degree energy boundary residual fits the retained chart, joining and closing allowances.

The proof uses the actual parent count, origin order one and the supplied target bound by one. -/
theorem energy_boundary_paid :
    Data.Gaussian.Norm.Basic.normSq (energy.connected.boundary - Path.BoundaryRibbon.area
      evaluated.chart.original.firstValue evaluated.chart.connected.summary.total) ≤
      160 * target + (((totalTarget / 4) / 4) / 4) + totalTarget := by
  have parentPositive : 0 < charts.parentTarget := by
    rw [charts.parentTarget_eq]
    exact Rational.Budget.Aggregate.perTerm_positive charts.positive _
  have bound := Hyperelliptic.Charts.Reciprocal.Disk.EnergyBoundaryControl.boundary_small
    energy.connected evaluated.chart.connected evaluated.chart.original.firstValue_eq branch
    parentPositive.le entry.request.budget.positive.le (entry.request.budget.tolerance_eq.trans_le
      (Fraction.Order.Basic.min_le_left _ _))
    (Fraction.Order.Field.div_nonneg_direct entry.positive.le (by decide))
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyBoundary.quarter_le entry.positive.le).trans small)
    entry.request.junctions evaluated.chart.original.junction_later entry.closing evaluated.closing_later
  have paid := add_le_add (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyBoundary.parent_paid (charts := charts))
    (by decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 160)) entry.request.budget.total_paid.le
  have combined := Fraction.Order.Arithmetic.add_le_add_right_direct paid (4 * (totalTarget / 4))
  have cancel : 4 * (totalTarget / 4) = totalTarget := by
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  rw [cancel] at combined
  calc
    _ ≤ 2 * ((entry.prepared.program.cache.parents.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 *
      (80 * charts.parentTarget + 2 * entry.request.budget.tolerance) +
      (80 * charts.parentTarget + 2 * (totalTarget / 4))) := bound
    _ = 160 * (((entry.prepared.program.cache.parents.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 + 1)
      * charts.parentTarget) +
      4 * (entry.prepared.program.cache.parents.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 *
        entry.request.budget.tolerance + totalTarget :=
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyBoundary.boundary_scale
          (entry.prepared.program.cache.parents.length : Normalization.InverseRootPolynomial.Coordinate)
          charts.parentTarget entry.request.budget.tolerance totalTarget
    _ ≤ 160 * target + (((totalTarget / 4) / 4) / 4) + totalTarget := combined

include branch small in
/-- The actual signed cap energy and closed polygon area satisfy their combined paid boundary and chart-error bound. -/
theorem closed_polygon_energy :
    Data.Gaussian.Norm.Basic.normSq (energy.connected.energy + evaluated.polygon.area) <
      2 * (256 * (4 * target + ((((totalTarget / 4) / 4) / 4) / 4) / 4) +
        (160 * target + (((totalTarget / 4) / 4) / 4) + totalTarget)) := by
  let residual := energy.connected.boundary - Path.BoundaryRibbon.area evaluated.chart.original.firstValue
    evaluated.chart.connected.summary.total
  let error := energy.connected.energy + evaluated.polygon.area - residual
  have close : Data.Gaussian.Norm.Basic.normSq error < 256 * (4 * target + ((((totalTarget / 4) / 4) / 4) / 4) / 4)
    :=
    (congrArg Data.Gaussian.Norm.Basic.normSq (by dsimp only [error, residual]; ring1)).trans_lt
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartEnergy.energy_polygon_close evaluated energy)
  have bounded : Data.Gaussian.Norm.Basic.normSq residual ≤ 160 * target + (((totalTarget / 4) / 4) / 4) +
    totalTarget := Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyBoundary.energy_boundary_paid evaluated energy
    branch small
  have sum := (add_le_add le_rfl bounded).trans_lt (Fraction.Order.Arithmetic.add_lt_add_right_direct close _)
  have estimate := (Gaussian.Norm.Bounds.normSq_add_le_two error residual).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 2) sum)
  exact (congrArg Data.Gaussian.Norm.Basic.normSq (by dsimp only [error]; ring1)).trans_lt estimate

include branch small in
/-- The original source area and signed cap energy satisfy the combined closed-polygon, chart and area comparison bound.
-/
theorem closed_source_energy :
    Data.Gaussian.Norm.Basic.normSq (energy.connected.energy + evaluated.chart.original.separated.left.area) <
      2 * (2 * (256 * (4 * target + ((((totalTarget / 4) / 4) / 4) / 4) / 4) +
        (160 * target + (((totalTarget / 4) / 4) / 4) + totalTarget)) + 2 * (areaTarget + target)) := by
  have close := Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyBoundary.closed_polygon_energy evaluated energy branch
    small
  have estimate := (Gaussian.Norm.Bounds.normSq_add_le_two (energy.connected.energy + evaluated.polygon.area)
    (evaluated.chart.original.separated.left.area - evaluated.polygon.area)).trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 2)
        (Fraction.Order.Arithmetic.add_lt_add_direct close evaluated.area_close))
  exact (congrArg Data.Gaussian.Norm.Basic.normSq (by ring1)).trans_lt estimate

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyBoundary
