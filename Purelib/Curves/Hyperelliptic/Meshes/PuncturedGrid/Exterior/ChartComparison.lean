module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceComparison
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalChartAcquisition
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

public section

/-!
# Chart replacement of the complete shared exterior boundary

Each block preserves its total exactly. All cross-block area terms therefore
cancel in the comparison; the remaining error is the sum of the retained
local area errors. The shared face readings and internal area correction are
those of the original surface evaluation.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {localTarget localArea chartTarget : Coordinate} {floor index depth readingIndex : Nat} {box :
    Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {shared :
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}

namespace ChartSamples.ChartedEntry

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry
/-- Assemble cached block summaries without reevaluating either path. -/
@[expose] def summary :
  (values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
  shared depth readingIndex localTarget localArea chartTarget floor)) →
    Path.IncrementArea.Summary (values.map (fun value => value.chart.path)).flatten
  | [] => Path.IncrementArea.Summary.build []
  | head :: tail => head.chart.summary.append (summary tail)

/-- Combining the original chart summaries preserves the exact total of the retained cap blocks. -/
theorem summary_total
  (values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
  shared depth readingIndex localTarget localArea chartTarget floor)) :
    (summary values).total =
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry.rightSummary
      (values.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.value)).total := by
  induction values with
  | nil => rfl
  | cons head tail ih => exact congrArg₂ (· + ·) head.total_preserved ih

/-- The complete chart-area difference is the sum of the actual block errors because their retained totals agree. -/
theorem
  summary_area_difference
  (values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
  shared depth readingIndex localTarget localArea chartTarget floor)) :
    (summary values).area -
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry.rightSummary
      (values.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.value)).area =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.map (fun value => value.chart.summary.area -
        value.value.evaluated.right.area)) := by
  induction values with
  | nil => change (0 : Gaussian) - 0 = 0; ring1
  | cons head tail ih =>
      change (head.chart.summary.area + (summary tail).area +
        Path.BoundaryRibbon.area head.chart.summary.total (summary tail).total) -
        (head.value.evaluated.right.area +
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry.rightSummary
          (tail.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.value)).area +
          Path.BoundaryRibbon.area head.value.evaluated.right.total
            (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry.rightSummary
            (tail.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.value)).total) =
        (head.chart.summary.area - head.value.evaluated.right.area) + _
      rw [head.total_preserved, Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.summary_total, ←
        ih]
      ring1

/-- The complete chart-area error satisfies the squared original block-count allowance. -/
theorem summary_area_error
  (values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
  shared depth readingIndex localTarget localArea chartTarget floor)) :
    normSq ((summary values).area -
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry.rightSummary
      (values.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.value)).area) ≤
      (values.length : Coordinate) * ((values.length : Coordinate) * chartTarget) := open Purelib in by
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.summary_area_difference]
  have estimate := Gaussian.Norm.Sum.Bounds.normSq_sum_le
    (values.map (fun value => value.chart.summary.area - value.value.evaluated.right.area)) chartTarget (by
      intro value member
      obtain ⟨entry, _, equal⟩ := Data.List.Map.mem_map.mp member
      rw [← equal]
      exact entry.area_error.le)
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
  simpa only [Data.List.Map.length_map] using estimate

end ChartSamples.ChartedEntry

namespace SurfaceRequests.AllSurfacePreparation.Request

variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {target areaTarget : Coordinate}

set_option genInjectivity false in
/-- The chart budget is additional to the original surface area budget. -/
structure
  ChartRequest
  (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request prepared target
  areaTarget floor) (chartTarget : Coordinate) where
  /-- The additional chart target is positive. -/ positive : 0 < chartTarget
  /-- The allocated allowance for each original chart block. -/ localChart : Coordinate
  /-- The local allowance is the original count-based allocation. -/ localChart_eq : localChart =
    Rational.Budget.Aggregate.perTerm chartTarget request.count
  /-- The chart requests on the original retained source entries. -/ requests :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartRequests localChart request.entries
  /-- The common required model index. -/ index : Nat
  /-- The index is exactly the maximum of the original surface and chart requirements. -/ index_eq : index = max
    request.index requests.maximum
  /-- The retained common chart depth. -/ depth : Nat
  /-- The depth equals the original chart-request maximum. -/ depth_eq : depth = requests.depthMaximum

constructive_injectivity ChartRequest

namespace ChartRequest

variable {request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request prepared
  target areaTarget floor}

/-- Allocate the additional chart target over the original request count and retain the common model index and depth. -/
@[expose] def
  build
  (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request prepared target
  areaTarget floor) (chartTarget : Coordinate) (positive : 0 < chartTarget) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.ChartRequest request
      chartTarget :=
  let localChart := Rational.Budget.Aggregate.perTerm chartTarget request.count
  let requests := Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartRequests.build localChart
    (Rational.Budget.Aggregate.perTerm_positive positive _) request.entries
  ⟨positive, localChart, rfl, requests, max request.index requests.maximum, rfl, requests.depthMaximum, rfl⟩

variable {charts :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.ChartRequest
  request chartTarget}

set_option genInjectivity false in
/-- The original chart plans on one retained cap sample, with their common reading stage. -/
structure
  Plan
  (charts : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.ChartRequest
  request chartTarget) (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) where
  /-- The original chart plans on the exact supplied sample. -/ plans :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartPlans sample charts.requests
  /-- The retained common reading stage. -/ stage : Nat
  /-- The stage is exactly the maximum of original surface and chart reading requirements. -/ stage_eq : stage = max
    request.readingIndex plans.maximum

constructive_injectivity Plan

namespace Plan

/-- Prepare every original chart on the supplied retained cap sample and cache the maximum reading stage. -/
@[expose] def
  build
  (charts : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.ChartRequest
  request chartTarget) (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.ChartRequest.Plan charts
  sample :=
  let plans := Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartPlans.build sample charts.requests
  ⟨plans, max request.readingIndex plans.maximum, rfl⟩

variable {plan :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.ChartRequest.Plan
  charts sample}

set_option genInjectivity false in
/-- The actual chart samples and original surface evaluation with their exact shared source identity.

The cached chart summary preserves the total and retains separate integral, source-area and corrected surface-area
comparisons. -/
structure
  Evaluation
  (plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.ChartRequest.Plan
  charts sample) (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index
  domains) (depth readingIndex : Nat) where
  /-- The actual original chart samples. -/ samples :
    ChartSamples request.entries sample shared depth
    readingIndex charts.localChart
  /-- The surface evaluation using those same retained original source samples. -/ original :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.Evaluation request sample
    shared depth readingIndex
  /-- The retained surface is exactly the original evaluation of the shared samples. -/ original_eq : original =
    request.evaluateWithSamples samples.original
  /-- The cached full chart-path summary. -/ summary : Path.IncrementArea.Summary (samples.values.map (fun value =>
    value.chart.path)).flatten
  /-- The chart summary total equals the original cap total. -/ total_preserved : summary.total = original.cap.total
  /-- The chart replacement area error is below the additional chart target. -/ area_error : normSq (summary.area -
    original.cap.area) < chartTarget
  /-- The actual integral differs from the chart total by less than the original target. -/ integral_close : normSq
    (original.integral - summary.total) < target
  /-- The actual source and chart areas satisfy the combined original and chart allowances. -/ source_area_close :
    normSq (original.source.area - summary.area) < 2 * (areaTarget + chartTarget)
  /-- The actual surface area with its retained internal correction satisfies the combined allowances. -/
    surface_area_close : normSq (original.surface.area + original.internalArea - summary.area) < 2 * (areaTarget +
    chartTarget)

constructive_injectivity Evaluation

/-- Both comparisons consume the identical source samples. Exact preservation
of block totals pays the whole exterior area, including cross-occurrence terms. -/
@[expose] def
  evaluate
  (plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.ChartRequest.Plan
  charts sample) (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index
  domains) (depth readingIndex : Nat)
    (later : charts.index ≤ index) (fineLater : charts.depth ≤ depth) (readingLater : plan.stage ≤ readingIndex) :

      Evaluation
      plan shared depth readingIndex := open Purelib.Data.Rat in by
  have positive : 0 < charts.localChart := charts.localChart_eq ▸ Rational.Budget.Aggregate.perTerm_positive
    charts.positive _
  let samples := plan.plans.evaluate positive
    ((Data.Nat.Order.le_max_right _ _).trans (charts.index_eq ▸ later)) (charts.depth_eq ▸ fineLater)
    ((Data.Nat.Order.le_max_right _ _).trans (plan.stage_eq ▸ readingLater)) (shared := shared)
  let original := request.evaluateWithSamples samples.original
  let summary := Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.summary samples.values
  have totalEq : summary.total = original.cap.total :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.summary_total samples.values
  have areaError : normSq (summary.area - original.cap.area) < chartTarget := by
    have estimate := Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.summary_area_error
      samples.values
    rw [samples.count_eq, request.count_entries] at estimate
    have paid : (request.count : Coordinate) * ((request.count : Coordinate) * charts.localChart) < chartTarget := by
      rw [charts.localChart_eq]
      exact Rational.Budget.Aggregate.count_mul_perTerm_lt charts.positive request.count
    exact estimate.trans_lt paid
  have reversed : Data.Gaussian.Norm.Basic.normSq (original.cap.area - summary.area) < chartTarget := by
    rw [show original.cap.area - summary.area = -(summary.area - original.cap.area) by ring1,
      Gaussian.Norm.Basic.normSq_neg]
    rw [Gaussian.Norm.Basic.normSq_eq_canonical]
    exact areaError
  have sourceClose : Data.Gaussian.Norm.Basic.normSq (original.source.area - summary.area) < 2 * (areaTarget +
    chartTarget) :=
    (Gaussian.Norm.Bounds.normSq_sub_le_via original.source.area original.cap.area summary.area).trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Coordinate) < 2)
        (Fraction.Order.Arithmetic.add_lt_add_direct original.area_close reversed))
  have surfaceClose : Data.Gaussian.Norm.Basic.normSq (original.surface.area + original.internalArea - summary.area)
    < 2 * (areaTarget + chartTarget) :=
    (Gaussian.Norm.Bounds.normSq_sub_le_via (original.surface.area + original.internalArea) original.cap.area
      summary.area).trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Coordinate) < 2)
        (Fraction.Order.Arithmetic.add_lt_add_direct original.surface_area_close reversed))
  have integralClose := original.integral_close
  rw [← totalEq, Gaussian.Norm.Basic.normSq_eq_canonical] at integralClose
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at sourceClose surfaceClose
  exact ⟨samples, original, rfl, summary, totalEq, areaError, integralClose, sourceClose, surfaceClose⟩

end Plan

set_option genInjectivity false in
/-- The actual cap sample, shared face bank, retained chart plan and its evaluation at the selected depth. -/
structure
  Acquisition
  (charts : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.ChartRequest
  request chartTarget) (depthFloor : Nat) where
  /-- The original cap sample acquired at the common index. -/ sample :
    Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential charts.index collar.box
  /-- The original shared face numerical bank at that same index. -/ shared :
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential charts.index domains
  /-- The actual chart plan on the retained sample. -/ plan :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.ChartRequest.Plan charts
    sample
  /-- The chosen subdivision depth. -/ depth : Nat
  /-- The depth is exactly the maximum of the requested floor and original chart depth. -/ depth_eq : depth = max
    depthFloor charts.depth
  /-- The actual retained evaluation at the chosen depth and sufficient reading stage. -/ evaluated :
    Plan.Evaluation
    plan shared depth plan.stage

constructive_injectivity Acquisition

/-- Build the original cap and shared face samples once, then evaluate the retained chart plan at its common stage. -/
@[expose] def
  acquire
  (charts : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.ChartRequest
  request chartTarget) (depthFloor : Nat) :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.ChartRequest.Acquisition
  charts depthFloor :=
  let sample := Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample.build cap differential charts.index collar.box
  let shared := Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.build differential charts.index
    domains
  let plan :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.ChartRequest.Plan.build
    charts sample
  let depth := max depthFloor charts.depth
  ⟨sample, shared, plan, depth, rfl, plan.evaluate shared depth plan.stage le_rfl (Data.Nat.Order.le_max_right _ _)
    le_rfl⟩

end ChartRequest
end SurfaceRequests.AllSurfacePreparation.Request
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
