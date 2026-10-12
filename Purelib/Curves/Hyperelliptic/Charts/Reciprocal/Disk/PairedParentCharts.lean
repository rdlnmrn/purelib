module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
public import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.ReciprocalDiskCommonSourceCharts
import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

public section

/-! The retained parent request supplies every common cover. Parent chart
comparisons share one cap sample pair and pay both finite aggregation levels.
The result retains corrections and does not discard cross-parent seam work. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib
open Purelib.Integration
open Purelib.Riemann
open Purelib.Data.Rat

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  {target : Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
  (original : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request regular other parents target minimum)

/-- The original retained paired parent plan at its certified finite index. -/
@[expose] def ChartParent (i : Fin original.plans.length) := original.plans[i.val]'i.isLt

/-- The actual common chart request on an original parent at its adjusted shared depth. -/
@[expose] def ChartPlanAt (depth : Nat) (allowance : Normalization.InverseRootPolynomial.Coordinate) (i : Fin
  original.plans.length) :=
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest regular
    (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent original i).common
    (original.localDepth (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent original i) depth)
      allowance minimum

/-- Every original parent's coarse depth plus its local refinement equals the common total depth. -/
theorem chartDepth_eq (depth : Nat) (i : Fin original.plans.length) :
    (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent original i).common.depth + original.localDepth
      (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent original i) depth = original.depth + depth :=
      by
  have member : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent original i ∈ original.plans :=
    List.getElem_mem i.isLt
  have lower : (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent original i).common.depth ≤
    original.depth := original.depth_eq ▸ Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan.depth_le member
  change (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent original i).common.depth + (original.depth
    - (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent original i).common.depth + depth) = _
  rw [← Nat.add_assoc, Data.Nat.Subtraction.add_sub_of_le lower]

/-- The sufficient stage of one original parent chart plan. -/
@[expose] def chartIndexWeight {depth : Nat} {allowance : Normalization.InverseRootPolynomial.Coordinate} (i : Fin
  original.plans.length)
    (plan : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartPlanAt original depth allowance i) : Nat :=
      plan.index

set_option genInjectivity false in
/-- A paid common chart request over the exact retained parent family.

It retains each original parent cover, a count-paid joining budget and one stage sufficient for both original and chart
requests. -/
structure ChartBankRequest (depth : Nat) (requested : Normalization.InverseRootPolynomial.Coordinate) where
  /-- The retained finite joining budget for the original parent count. -/ joinBudget :
    Normalization.ReciprocalDiskCommonSourceCharts.SourceComparisonRequest.PathReplacement.JoinBudget
    original.plans.length requested
  /-- The common local parent chart allowance. -/ allowance : Normalization.InverseRootPolynomial.Coordinate
  /-- The local allowance is exactly the retained joining allocation. -/ allowance_eq : allowance = joinBudget.allowance
  /-- The common local allowance is positive. -/ positive : 0 < allowance
  /-- The complete original parent-count-squared charge fits the requested target. -/ paid : (original.plans.length :
    Normalization.InverseRootPolynomial.Coordinate) * ((original.plans.length :
    Normalization.InverseRootPolynomial.Coordinate) * allowance) < requested
  /-- The actual chart requests on the original parent plans. -/ plans : Data.Vector.DependentVector
    (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartPlanAt original depth allowance)
  /-- The cached common sufficient parent and chart stage. -/ index : Nat
  /-- The common stage is the maximum of the original request index and actual parent chart indices. -/ index_eq : index
    = max original.index (plans.maximum (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.chartIndexWeight
    original))

constructive_injectivity ChartBankRequest

namespace ChartBankRequest

/-- Prepare common chart requests on the original parent covers and retain their paid joining budget with one sufficient
stage. -/
@[expose] def build (depth : Nat) (requested : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 <
  requested) :
    Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest original depth requested :=
  let joinBudget :=
    Normalization.ReciprocalDiskCommonSourceCharts.SourceComparisonRequest.PathReplacement.JoinBudget.build
    original.plans.length requested positive
  let allowance := joinBudget.allowance
  have allowancePositive := joinBudget.positive
  let plans := Data.Vector.DependentVector.ofFn (fun i =>
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest.build
    regular (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent original i).common
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation.ChartPreparation.build regular
      (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent original i).common)
    (original.localDepth (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent original i) depth)
      allowance allowancePositive minimum)
  ⟨joinBudget, allowance, rfl, allowancePositive, joinBudget.count_paid,
    plans, max original.index (plans.maximum (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.chartIndexWeight
      original)), rfl⟩

variable {original} {depth : Nat} {requested : Normalization.InverseRootPolynomial.Coordinate}
  (request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest original depth
    requested)

/-- The original paired parent request is valid at the retained chart-bank stage. -/
theorem original_le : original.index ≤ request.index := by
  rw [request.index_eq]
  exact Data.Nat.Order.le_max_left _ _

/-- The dependent vector of actual retained parent chart evaluations at the common stage. -/
@[expose] def Entries := Data.Vector.DependentVector (fun i =>
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest.Evaluation (request.plans.get i) request.index)

/-- Evaluate each original parent chart using the same supplied cap sample pair. -/
@[expose] def evaluateEntries (firstCap : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential
  request.index collar.box)
    (otherCap : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other request.index collar.box) :
      request.Entries :=
  Data.Vector.DependentVector.ofFn (fun i =>
    let plan := Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent original i
    let samples := Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.SampleBank.ofCapSamples
      (cover := plan.left) (otherCover := plan.right) firstCap otherCap
    (request.plans.get i).evaluate samples
      ((Data.Vector.DependentVector.get_le_maximum
        (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.chartIndexWeight original) request.plans i).trans
        ((Data.Nat.Order.le_max_right _ _).trans_eq request.index_eq.symm)) 0)

/-- Every retained parent evaluation uses exactly the supplied original cap sample pair. -/
@[expose] def SharedCaps (entries : request.Entries)
    (firstCap : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential request.index collar.box)
    (otherCap : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other request.index collar.box) : Prop :=
  ∀ i, (entries.get i).samples.firstCap = firstCap ∧ (entries.get i).samples.otherCap = otherCap

/-- Evaluating the parent entries preserves the same supplied cap samples in every entry. -/
theorem evaluateEntries_shared (firstCap : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential
  request.index collar.box)
    (otherCap : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other request.index collar.box) :
    request.SharedCaps (request.evaluateEntries firstCap otherCap) firstCap otherCap := by
  intro i
  dsimp only [Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.evaluateEntries, -eq_self,
    -iff_self]
  rw [Data.Vector.DependentVector.ofFn_get]
  rw [Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest.evaluate_samples]
  exact ⟨rfl, rfl⟩

set_option genInjectivity false in
/-- The actual shared-cap parent evaluations with cached source, chart and correction areas and their paid bounds. -/
structure Evaluation where
  /-- The single retained first-differential cap sample. -/ firstCap :
    Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential request.index collar.box
  /-- The single retained other-differential cap sample. -/ otherCap :
    Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other request.index collar.box
  /-- The actual original parent chart evaluations. -/ entries : request.Entries
  /-- Every entry retains the same two cached cap samples. -/ shared : request.SharedCaps entries firstCap otherCap
  /-- The cached total original source area. -/ sourceArea : Normalization.InverseRootPolynomial.Gaussian
  /-- The source area is the finite sum of the actual retained parent source areas. -/ sourceArea_eq : sourceArea =
    FiniteSum.Fin.sumFin (fun i => (entries.get i).sourceArea)
  /-- The cached total original chart area. -/ chartArea : Normalization.InverseRootPolynomial.Gaussian
  /-- The chart area is the finite sum of the actual retained parent chart areas. -/ chartArea_eq : chartArea =
    FiniteSum.Fin.sumFin (fun i => (entries.get i).chartArea)
  /-- The cached complete parent chart correction. -/ correction : Normalization.InverseRootPolynomial.Gaussian
  /-- The correction is the finite sum of the original retained parent corrections. -/ correction_eq : correction =
    FiniteSum.Fin.sumFin (fun i => (entries.get i).correction)
  /-- The actual source-minus-chart-minus-correction discrepancy meets the whole target. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq (sourceArea - chartArea - correction) < requested
  /-- The cached total original centered source area. -/ sourceCenteredArea :
    Normalization.InverseRootPolynomial.Gaussian
  /-- The centered source area is the finite sum of the actual retained parent values. -/ sourceCenteredArea_eq :
    sourceCenteredArea = FiniteSum.Fin.sumFin (fun i => (entries.get i).sourceCenteredArea)
  /-- The cached total original centered chart area. -/ chartCenteredArea : Normalization.InverseRootPolynomial.Gaussian
  /-- The centered chart area is the finite sum of the actual retained parent values. -/ chartCenteredArea_eq :
    chartCenteredArea = FiniteSum.Fin.sumFin (fun i => (entries.get i).chartCenteredArea)
  /-- The actual centered source-to-chart discrepancy meets the whole target. -/ centered_bounded :
    Data.Gaussian.Norm.Basic.normSq (sourceCenteredArea - chartCenteredArea) < requested

constructive_injectivity Evaluation

/-- Both cap polynomials are sampled once for the complete retained parent
family. Each parent reuses them in its cached reciprocal primitive bank. -/
@[expose] def acquire : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation request :=
  by
  let firstCap := Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample.build cap differential request.index collar.box
  let otherCap := Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample.build cap other request.index collar.box
  let entries := request.evaluateEntries firstCap otherCap
  let sourceArea := FiniteSum.Fin.sumFin (fun i => (entries.get i).sourceArea)
  let chartArea := FiniteSum.Fin.sumFin (fun i => (entries.get i).chartArea)
  let correction := FiniteSum.Fin.sumFin (fun i => (entries.get i).correction)
  have estimate := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le
    (fun i => (entries.get i).sourceArea - (entries.get i).chartArea - (entries.get i).correction)
    request.allowance (fun i => (entries.get i).bounded.le)
  rw [FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_sub] at estimate
  have paid : (original.plans.length : Normalization.InverseRootPolynomial.Coordinate)^2 * request.allowance < requested
    :=
    (by ring1 : (original.plans.length : Normalization.InverseRootPolynomial.Coordinate)^2 * request.allowance =
      (original.plans.length : Normalization.InverseRootPolynomial.Coordinate) * ((original.plans.length :
        Normalization.InverseRootPolynomial.Coordinate) * request.allowance)).trans_lt request.paid
  let sourceCenteredArea := FiniteSum.Fin.sumFin (fun i => (entries.get i).sourceCenteredArea)
  let chartCenteredArea := FiniteSum.Fin.sumFin (fun i => (entries.get i).chartCenteredArea)
  have centered := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le
    (fun i => (entries.get i).sourceCenteredArea - (entries.get i).chartCenteredArea)
    request.allowance (fun i => (entries.get i).centered_bounded.le)
  rw [FiniteSum.Fin.sumFin_sub] at centered
  exact ⟨firstCap, otherCap, entries, request.evaluateEntries_shared firstCap otherCap,
    sourceArea, rfl, chartArea, rfl, correction, rfl, estimate.trans_lt paid,
    sourceCenteredArea, rfl, chartCenteredArea, rfl, centered.trans_lt paid⟩

/-- Every original parent source area uses the retained common total depth. -/
theorem Evaluation.source_depth (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation request) (i : Fin
  original.plans.length) :
    (evaluated.entries.get i).sourceArea = Periods.DyadicBilinearBoundaryRibbon.dyadicArea
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues (evaluated.entries.get
        i).samples.source (evaluated.entries.get i).samples.otherSource)
      (original.depth + depth) 0 1 := by
  have full := (evaluated.entries.get i).sourceArea_full
  rw [Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.chartDepth_eq original depth i] at full
  exact full

/-- The retained parent polygons are recovered from cached fine and local
centered areas. This does not discard the remaining between-parent terms. -/
@[expose] def Evaluation.coarseSourceArea (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation request) : Gaussian :=
  evaluated.sourceArea - evaluated.sourceCenteredArea

/-- The cached coarse source area equals the finite sum of the retained parent coarse areas. -/
theorem Evaluation.coarseSourceArea_eq (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation request) :
    evaluated.coarseSourceArea = FiniteSum.Fin.sumFin (fun i => (evaluated.entries.get i).coarseSourceArea) := by
  unfold Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation.coarseSourceArea
  rw [evaluated.sourceArea_eq, evaluated.sourceCenteredArea_eq, ← FiniteSum.Fin.sumFin_sub]
  rfl

/-- The cached coarse source area is the actual original parent dyadic area sum at each retained coarse depth. -/
theorem Evaluation.coarseSourceArea_full (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation request) :
    evaluated.coarseSourceArea = FiniteSum.Fin.sumFin (fun i => Periods.DyadicBilinearBoundaryRibbon.dyadicArea
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues (evaluated.entries.get
        i).samples.source (evaluated.entries.get i).samples.otherSource)
      (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent original i).common.depth 0 1) := by
  rw [Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation.coarseSourceArea_eq]
  exact FiniteSum.Fin.sumFin_congr (fun i => (evaluated.entries.get i).coarseSourceArea_eq)

/-- Subtracting the exact retained coarse source area leaves the paid centered chart comparison. -/
theorem Evaluation.coarse_centered_bounded (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation request) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.sourceArea - evaluated.coarseSourceArea -
      evaluated.chartCenteredArea) < requested := by
  have equal : evaluated.sourceArea - evaluated.coarseSourceArea = evaluated.sourceCenteredArea := by
    unfold Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation.coarseSourceArea
    ring1
  rw [equal]
  exact evaluated.centered_bounded

/-- The ordered original parent increment paths at the common total depth. -/
@[expose] def Evaluation.sourcePaths (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation request) :=
  List.ofFn (fun i : Fin original.plans.length => Path.Dyadic.DyadicPairedPrimitivePaths.increments
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues (evaluated.entries.get
      i).samples.source (evaluated.entries.get i).samples.otherSource)
    (original.depth + depth) 0 1)

/-- Compose every parent replacement in the retained order. Equal source
totals preserve the polygon of parent increments exactly. -/
@[expose] def Evaluation.joinedCharts (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation request) :
    Normalization.ReciprocalDiskCommonSourceCharts.SourceComparisonRequest.PathReplacement evaluated.sourcePaths.flatten
      := by
  let paths := fun i : Fin original.plans.length => (evaluated.entries.get i).sourceBlocks.flatten
  have pathsEq : List.ofFn paths = evaluated.sourcePaths := by
    apply Data.List.OfFn.Basic.ofFn_congr
    intro i
    have full := (evaluated.entries.get i).sourceBlocks_full
    rw [Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.chartDepth_eq original depth i] at full
    exact full
  exact Normalization.ReciprocalDiskCommonSourceCharts.SourceComparisonRequest.PathReplacement.readback (congrArg
    List.flatten pathsEq)
    (Normalization.ReciprocalDiskCommonSourceCharts.SourceComparisonRequest.PathReplacement.join paths (fun i =>
      (evaluated.entries.get i).joinedCharts))

/-- The actual joined chart replacement's retained bound is strictly below the whole target. -/
theorem Evaluation.joinedCharts_paid (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation request) :
    (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation.joinedCharts request
      evaluated).bound < requested := by
  have bound := Normalization.ReciprocalDiskCommonSourceCharts.SourceComparisonRequest.PathReplacement.join_bound _ (fun
    i => (evaluated.entries.get i).joinedCharts)
    (fun i => (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest.Evaluation.joinedCharts_paid
      (request.plans.get i) (evaluated.entries.get i)).le)
  have paid := (congrArg₂ (fun a b : Normalization.InverseRootPolynomial.Coordinate => a * b)
    request.joinBudget.rate_eq.symm request.allowance_eq).trans_lt
    request.joinBudget.join_paid
  exact bound.trans_lt paid

/-- The actual joined chart preserves the complete original source path total. -/
theorem Evaluation.joinedCharts_total (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation request) :
    (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation.joinedCharts request
      evaluated).chart.totalValue = Path.PairedIncrementArea.total evaluated.sourcePaths.flatten := by
  rw [(Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation.joinedCharts request
    evaluated).total_eq,
    (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation.joinedCharts request
    evaluated).source.total_eq]

/-- The complete original source path area and retained joined chart area meet the actual replacement bound. -/
theorem Evaluation.joinedCharts_bounded (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation request) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area evaluated.sourcePaths.flatten -
      (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation.joinedCharts request
        evaluated).chart.areaValue) ≤
        (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation.joinedCharts request
        evaluated).bound := by
  rw [← (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation.joinedCharts request
    evaluated).source.area_eq]
  exact (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation.joinedCharts request
    evaluated).bounded

/-- The complete original source path area and retained joined chart area meet the requested whole target. -/
theorem Evaluation.joinedCharts_accurate (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation request) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area evaluated.sourcePaths.flatten -
      (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation.joinedCharts request
        evaluated).chart.areaValue) < requested :=
  (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation.joinedCharts_bounded request
    evaluated).trans_lt
    (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation.joinedCharts_paid request
    evaluated)

end ChartBankRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
