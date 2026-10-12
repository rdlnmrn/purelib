module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartClosure
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyBoundary
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Data.Gaussian.Basic
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

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Riemann

@[expose] public section

/-!
# Automatic requested odd cap energy for an actual exterior program

The request chooses its comparison tolerances internally, preserves the
prepared program and its original source area, and pays all endpoint and
closing corrections. The same cached fan energy supplies the lower bound.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RequestedEnergy

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

/-- Quartering a rational value below a positive target preserves that target bound. -/
private theorem quarter_step {target value : Normalization.InverseRootPolynomial.Coordinate} (positive : 0 < target)
  (bound : value ≤ target) : value / 4 ≤ target := by
  have quarter : target / 4 ≤ target := by
    apply (Fraction.Order.Field.div_le_iff_pos (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 4)).mpr
    exact (show target = target * 1 by ring1).trans_le
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide) positive.le)
  have ordered := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct bound
    (Fraction.Order.Field.inv_pos_direct (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 4)).le
  exact (show value / 4 = value * (4 : Normalization.InverseRootPolynomial.Coordinate)⁻¹ from
    Fraction.Field.div_eq_mul_inv_direct _ _).trans_le
    (ordered.trans (by simpa only [Fraction.Field.div_eq_mul_inv_direct] using quarter))

/-- The explicit original odd cap polygon and source comparison charges are bounded by the common factor 16384. -/
public theorem comparison_paid {q : Normalization.InverseRootPolynomial.Coordinate} (positive : 0 < q) :
    2 * (256 * (4 * q + ((((q / 4) / 4) / 4) / 4) / 4) + (160 * q + (((q / 4) / 4) / 4) + q)) ≤ 16384 * q ∧
    2 * (2 * (256 * (4 * q + ((((q / 4) / 4) / 4) / 4) / 4) + (160 * q + (((q / 4) / 4) / 4) + q)) + 2 * (q + q)) ≤
      16384 * q := by
  have third := Hyperelliptic.Meshes.PuncturedGrid.Exterior.RequestedEnergy.quarter_step positive
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.RequestedEnergy.quarter_step positive
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.RequestedEnergy.quarter_step positive le_rfl))
  have fifth := Hyperelliptic.Meshes.PuncturedGrid.Exterior.RequestedEnergy.quarter_step positive
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.RequestedEnergy.quarter_step positive third)
  have chart := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add (le_rfl : 4 * q ≤ 4 * q) fifth)
    (Fraction.Cast.Order.natCast_le_direct (by decide : 0 ≤ 256))
  have boundary := Fraction.Order.Arithmetic.add_le_add_right_direct (add_le_add (le_rfl : 160 * q ≤ 160 * q) third) q
  have polygon := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add chart boundary) (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
  have source := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_right_direct polygon (2 * (q + q))) (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
  refine ⟨polygon.trans ((by ring1 : 2 * (256 * (4 * q + q) + (160 * q + q + q)) = 2884 * q).trans_le ?_),
    source.trans ((by ring1 : 2 * (2 * (256 * (4 * q + q) + (160 * q + q + q)) + 2 * (q + q)) = 5776 * q).trans_le ?_)⟩
  · exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (Fraction.Cast.Order.natCast_le_direct (by
      decide : 2884 ≤ 16384)) positive.le
  · exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (Fraction.Cast.Order.natCast_le_direct (by
      decide : 5776 ≤ 16384)) positive.le

set_option genInjectivity false in
/-- The actual odd-degree cap energy with internally allocated comparison tolerances and the original source and polygon
error bounds.

The preparation identity and cached energy lower bound remain attached to the same retained program. -/
structure OddEnergyAcquisition (prepared : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.PreparedProgram
  regular lifted differential)
    (target energyTarget : Normalization.InverseRootPolynomial.Coordinate) (minimum depthFloor energyFloor : Nat) where
  /-- The retained common local comparison target. -/ comparisonTarget : Normalization.InverseRootPolynomial.Coordinate
  /-- The local comparison target is positive. -/ comparison_positive : 0 < comparisonTarget
  /-- The local comparison target is at most one. -/ comparison_small : comparisonTarget ≤ 1
  /-- The complete fixed-factor comparison charge fits the supplied target. -/ comparison_paid : 16384 *
    comparisonTarget ≤ target
  /-- The original prepared exterior entry at the retained local tolerance. -/ entry :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Entry regular lifted differential comparisonTarget
    comparisonTarget minimum
  /-- The entry retains exactly the supplied original prepared program. -/ prepared_eq : entry.prepared = prepared
  /-- The actual chart acquisition on that same retained exterior entry. -/ charts :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartClosure.ChartAcquisition entry comparisonTarget depthFloor
  /-- The cached requested energy on the actual retained chart. -/ energy :
    Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy.RequestedEnergy charts.evaluated.chart energyTarget energyFloor
  /-- The cached energy satisfies the requested imaginary-part lower bound. -/ lower : -energyTarget <
    energy.connected.energy.im / 4
  /-- The actual closed polygon and cached energy satisfy the supplied comparison target. -/ polygon_close :
    Data.Gaussian.Norm.Basic.normSq (energy.connected.energy + charts.evaluated.polygon.area) < target
  /-- The original source area and cached energy satisfy the supplied comparison target. -/ source_close :
    Data.Gaussian.Norm.Basic.normSq (energy.connected.energy + charts.evaluated.chart.original.separated.left.area)
    < target

constructive_injectivity OddEnergyAcquisition

/-- Acquire the complete odd cap energy from positive requests, using the
original root-closed program, source area, and all retained parent owners. -/
def PreparedProgram.acquireOddEnergy (prepared :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.PreparedProgram regular lifted differential)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (target energyTarget : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) (energyPositive : 0 <
      energyTarget)
    (minimum depthFloor energyFloor : Nat) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.RequestedEnergy.OddEnergyAcquisition prepared target energyTarget
      minimum depthFloor energyFloor := by
  let q := min 1 (target / 16384)
  have scalePositive : (0 : Normalization.InverseRootPolynomial.Coordinate) < 16384 :=
    Fraction.Cast.Order.natCast_pos_direct (by decide : 0 < 16384)
  have qPositive : 0 < q := Fraction.Order.Basic.lt_min (by decide) (Fraction.Order.Field.div_pos_direct positive
    scalePositive)
  have qSmall : q ≤ 1 := Fraction.Order.Basic.min_le_left _ _
  have paid : 16384 * q ≤ target := by
    have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.min_le_right (1 :
      Normalization.InverseRootPolynomial.Coordinate) (target / 16384))
      scalePositive.le
    exact bound.trans_eq (by
        rw [Fraction.Field.mul_comm];
        exact Fraction.Field.div_mul_cancel_of_ne _ _ (ne_of_gt scalePositive))
  let entry := Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Entry.build prepared q q qPositive qPositive
    minimum
  let charts := Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartClosure.acquireCharts entry q qPositive depthFloor
  let energy := Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartEnergy.energy charts.evaluated branch energyTarget
    energyPositive energyFloor
  have budgets := Hyperelliptic.Meshes.PuncturedGrid.Exterior.RequestedEnergy.comparison_paid qPositive
  exact ⟨q, qPositive, qSmall, paid, entry, rfl, charts, energy,
    Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy.RequestedEnergy.lower energy,
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyBoundary.closed_polygon_energy charts.evaluated energy branch
      qSmall).trans_le (budgets.1.trans paid),
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyBoundary.closed_source_energy charts.evaluated energy branch
      qSmall).trans_le (budgets.2.trans paid)⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RequestedEnergy
