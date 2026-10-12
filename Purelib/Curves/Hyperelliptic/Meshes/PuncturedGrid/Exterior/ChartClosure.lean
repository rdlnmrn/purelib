module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaClosure
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts.ChartRequest
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison
open Purelib.Integration.Path
open Purelib.Integration.Path.IncrementAreaClosure

/-!
# Closed chart polygons on the actual exterior period components

The original complete component supplies its retained root return, including
both laps in odd degree. Chart acquisition reuses that component's source
and root readings. Closing the full replacement preserves its internal area
and compares with the same scheduled exterior period sample.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartClosure

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison (Entry SampledEntry)
open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {totalTarget areaTarget target
    : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
  {entry : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Entry regular lifted differential
    totalTarget areaTarget minimum}
  {charts : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts.ChartRequest entry.request target}
  {index : Nat} {box : Purelib.Geometry.Rational.Box} {sample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

set_option genInjectivity false in
/-- A complete original exterior component's chart plan and root-return stage.

The common stage pays both the retained chart evaluation and the original component's closing request. -/
structure ChartPlan (entry : CapComparison.Entry regular lifted differential totalTarget areaTarget minimum)
    (charts : ConnectedCharts.ChartRequest entry.request target)
    (sample : Primitives.Sample cap differential index box) where
  /-- The original chart evaluation plan for the retained exterior entry and cap sample. -/ chart : ChartRequest.Plan
    charts sample
  /-- The cached common chart and root-return reading stage. -/ stage : Nat
  /-- The retained stage is the maximum of the actual chart stage and original root-return maximum. -/ stage_eq : stage
    = max chart.stage entry.closing.maximum

constructive_injectivity ChartPlan

namespace ChartPlan

/-- Prepare the actual exterior chart evaluation and cache a stage paying the original component's root return. -/
@[expose] def build (entry : CapComparison.Entry regular lifted differential totalTarget areaTarget minimum)
    (charts : ConnectedCharts.ChartRequest entry.request target)
    (sample : Primitives.Sample cap differential index box) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartClosure.ChartPlan entry charts sample :=
  let chart := Plan.build charts sample
  ⟨chart, max chart.stage entry.closing.maximum, rfl⟩

variable {plan : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartClosure.ChartPlan entry charts sample}
  {depth readingIndex : Nat}

set_option genInjectivity false in
/-- The actual closed chart replacement of one retained exterior component.

It retains the original sampled period and chart evaluation, exact zero total and area readback, and separate area,
period and coordinate-return estimates. -/
structure Evaluation (plan : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartClosure.ChartPlan entry charts
  sample) (depth readingIndex : Nat) where
  /-- The actual retained chart evaluation at the supplied depth and reading stage. -/ chart : Plan.Evaluation
    plan.chart depth readingIndex
  /-- The sampled original exterior period component on the same retained cap sample. -/ original :
    CapComparison.SampledEntry regular lifted sample totalTarget areaTarget minimum depth readingIndex
  /-- The original sample retains exactly the supplied exterior entry. -/ original_entry : original.entry = entry
  /-- The original entry sample reuses the actual chart evaluation's original result. -/ original_result : HEq
    original.result chart.original
  /-- The closed summary of the actual connected replacement paths and their final closing increment. -/ polygon :
    IncrementArea.Summary (chart.connected.paths.flatten ++ [-chart.connected.summary.total])
  /-- The complete retained replacement polygon has total zero. -/ total_zero : polygon.total = 0
  /-- Closing preserves the actual connected replacement summary's area. -/ area_eq : polygon.area =
    chart.connected.summary.area
  /-- The original source area and closed chart area satisfy the combined original area and chart allowance. -/
    area_close : Data.Gaussian.Norm.Basic.normSq (chart.original.separated.left.area - polygon.area) < 2 *
    (areaTarget + target)
  /-- The original scheduled period sample is close to the retained closed polygon total. -/ period_close :
    Data.Gaussian.Norm.Basic.normSq (original.period.sample - polygon.total) < totalTarget
  /-- The actual reading stage pays the original component's root-return maximum. -/ closing_later :
    entry.closing.maximum ≤ readingIndex
  /-- The original source coordinates return within the retained reciprocal collar allowance. -/ coordinate_closing :
    Data.Gaussian.Norm.Basic.normSq (chart.original.coordinates.first - chart.original.coordinates.last) <
    collar.coordinateBound / 64

constructive_injectivity Evaluation

/-- Evaluate the retained chart and original period at the paid stage, then close the actual connected chart path. -/
@[expose] def evaluate (plan : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartClosure.ChartPlan entry charts
  sample) (depth readingIndex : Nat)
    (later : charts.index ≤ index) (fineLater : charts.depth ≤ depth) (readingLater : plan.stage ≤ readingIndex) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartClosure.ChartPlan.Evaluation plan depth readingIndex := by
  have stages := plan.stage_eq.ge.trans readingLater
  let chart := plan.chart.evaluate depth readingIndex later fineLater ((Data.Nat.Order.le_max_left _ _).trans stages)
  let original := SampledEntry.build entry chart.original ((Data.Nat.Order.le_max_right _ _).trans stages)
  let polygon := Summary.close chart.connected.summary
  refine ⟨chart, original, rfl, HEq.rfl, polygon, rfl, rfl, chart.area_close, ?_, (Data.Nat.Order.le_max_right _
    _).trans stages, original.coordinate_closing⟩
  have close := original.integral_close
  rw [original.polygon_total] at close
  exact close

end ChartPlan

set_option genInjectivity false in
/-- The fully prepared and evaluated closed chart component at a retained depth floor.

The original entry, computed cap sample, chart request and maximum depth remain the owners of the cached evaluation. -/
structure ChartAcquisition (entry : CapComparison.Entry regular lifted differential totalTarget areaTarget minimum)
    (target : InverseRootPolynomial.Coordinate) (depthFloor : Nat) where
  /-- The actual positive chart request on the original exterior entry. -/ request : ConnectedCharts.ChartRequest
    entry.request target
  /-- The cached cap primitive sample at the chart request's original stage and collar box. -/ sample :
    Primitives.Sample cap differential request.index collar.box
  /-- The chart and closing plan for that exact retained cap sample. -/ plan :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartClosure.ChartPlan entry request sample
  /-- The cached common evaluation depth. -/ depth : Nat
  /-- The evaluation depth is the maximum of the supplied floor and original chart depth. -/ depth_eq : depth = max
    depthFloor request.depth
  /-- The cached closed evaluation at the retained depth and common reading stage. -/ evaluated :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartClosure.ChartPlan.Evaluation plan depth plan.stage

constructive_injectivity ChartAcquisition

/-- Prepare the complete closed chart component from positive requests, with computed source, mesh, root-reading and
root-return stages. -/
@[expose] def acquireCharts (entry : CapComparison.Entry regular lifted differential totalTarget areaTarget minimum)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (depthFloor : Nat) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartClosure.ChartAcquisition entry target depthFloor :=
  let request := ChartRequest.build entry.request target positive
  let sample := Primitives.Sample.build cap differential request.index collar.box
  let plan := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartClosure.ChartPlan.build entry request sample
  let depth := max depthFloor request.depth
  ⟨request, sample, plan, depth, rfl, plan.evaluate depth plan.stage le_rfl (Data.Nat.Order.le_max_right _ _) le_rfl⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartClosure
