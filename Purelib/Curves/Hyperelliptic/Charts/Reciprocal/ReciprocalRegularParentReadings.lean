module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.List.Map
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBlockComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.JoinedTraceIncrements
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Path.PairedIncrementComparison
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.Topology.PreparedRefinementRootChains
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.JoinedTrace
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Raise only the chart-reading floor while retaining the parent bank's
source samples and both cap polynomials. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentReadings

open Purelib
open Purelib.Algebra
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace
open Purelib.Data.Gaussian.Norm.Sum
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Data.Vector
open Purelib.Geometry.Path.Gaussian
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Integration.Path.JoinedTraceIncrements
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Riemann.Topology

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest (Request)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts (ChartBankRequest ChartParent)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily (CommonRibbonRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints (RegularEndpointRequest)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : RegularBounds.Data cap}
  {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  {target requested : Coordinate} {minimum depth : Nat}
  {original : Request regular other parents
    target minimum}
  {request : ChartBankRequest original depth
    requested}

/-- Acquire later chart readings for every retained parent while reusing its exact original source and cap samples. -/
@[expose] def Evaluation.rereadEntries (evaluated : request.Evaluation) (floor : Nat) : request.Entries :=
  DependentVector.ofFn (fun i => (request.plans.get i).evaluate
    (evaluated.entries.get i).samples (evaluated.entries.get i).later floor)

/-- Reuse the numerical source/cap bank, selecting later chart readings only. -/
@[expose] def Evaluation.atReadingFloor (evaluated : request.Evaluation) (floor : Nat) : request.Evaluation := by
  let firstCap := evaluated.firstCap
  let otherCap := evaluated.otherCap
  let entries := Evaluation.rereadEntries
    evaluated floor
  have shared : request.SharedCaps entries firstCap otherCap := by
    intro i
    dsimp only [entries,
      Evaluation.rereadEntries, -eq_self,
      -iff_self]
    rw [DependentVector.ofFn_get, ChartRequest.evaluate_samples]
    exact evaluated.shared i
  let sourceArea := sumFin (fun i => (entries.get i).sourceArea)
  let chartArea := sumFin (fun i => (entries.get i).chartArea)
  let correction := sumFin (fun i => (entries.get i).correction)
  have estimate := Indexed.normSq_sumFin_le
    (fun i => (entries.get i).sourceArea - (entries.get i).chartArea - (entries.get i).correction)
    request.allowance (fun i => (entries.get i).bounded.le)
  rw [sumFin_sub, sumFin_sub] at estimate
  have paid : (original.plans.length : Coordinate)^2 * request.allowance < requested :=
    (by ring1 : (original.plans.length : Coordinate)^2 * request.allowance =
      (original.plans.length : Coordinate) * ((original.plans.length :
        Coordinate) * request.allowance)).trans_lt request.paid
  let sourceCenteredArea := sumFin (fun i => (entries.get i).sourceCenteredArea)
  let chartCenteredArea := sumFin (fun i => (entries.get i).chartCenteredArea)
  have centered := Indexed.normSq_sumFin_le
    (fun i => (entries.get i).sourceCenteredArea - (entries.get i).chartCenteredArea)
    request.allowance (fun i => (entries.get i).centered_bounded.le)
  rw [sumFin_sub] at centered
  exact ⟨firstCap, otherCap, entries, shared,
    sourceArea, rfl, chartArea, rfl, correction, rfl, estimate.trans_lt paid,
    sourceCenteredArea, rfl, chartCenteredArea, rfl, centered.trans_lt paid⟩

/-- Every actual first endpoint stage in the reread bank is above the requested reading floor. -/
theorem Evaluation.atReadingFloor_firstStage (evaluated : request.Evaluation) (floor : Nat)
    (i : Fin original.plans.length) : floor ≤ Evaluation.firstStage
      (Evaluation.atReadingFloor evaluated floor)
      i := by
  change floor ≤ (((Evaluation.rereadEntries
    evaluated floor).get i).entries.get
    (ChartParent original i).common.firstIndex).evaluated.chart.retained.area.refined.stage
  rw [Evaluation.rereadEntries,
    DependentVector.ofFn_get]
  exact ((request.plans.get i).evaluate (evaluated.entries.get i).samples
    (evaluated.entries.get i).later floor).readingsLater _

/-- Every actual last endpoint stage in the reread bank is above the requested reading floor. -/
theorem Evaluation.atReadingFloor_lastStage (evaluated : request.Evaluation) (floor : Nat)
    (i : Fin original.plans.length) : floor ≤ Evaluation.lastStage
      (Evaluation.atReadingFloor evaluated floor)
      i := by
  change floor ≤ (((Evaluation.rereadEntries
    evaluated floor).get i).entries.get
    (ChartParent original i).common.lastIndex).evaluated.chart.retained.area.refined.stage
  rw [Evaluation.rereadEntries,
    DependentVector.ofFn_get]
  exact ((request.plans.get i).evaluate (evaluated.entries.get i).samples
    (evaluated.entries.get i).later floor).readingsLater _

/-- Raising the chart-reading floor preserves the literal raw source path, including its dyadic depth and parent order.
-/
theorem Evaluation.atReadingFloor_sourcePaths (evaluated : request.Evaluation) (floor : Nat) :
    (Evaluation.atReadingFloor evaluated
      floor).sourcePaths = evaluated.sourcePaths := by
  apply OfFn.Basic.ofFn_congr
  intro i
  change DyadicPairedPrimitivePaths.increments
    (CommonRibbonRequest.sourceValues
      ((Evaluation.rereadEntries evaluated
      floor).get i).samples.source
      ((Evaluation.rereadEntries evaluated
        floor).get i).samples.otherSource)
    (original.depth + depth) 0 1 = _
  rw [Evaluation.rereadEntries,
    DependentVector.ofFn_get,
    ChartRequest.evaluate_samples]

/-- The existing block comparison applies to the actual raw source segment of each retained parent, without a radial
boundary certificate. -/
theorem Evaluation.parent_source_total_bound (evaluated : request.Evaluation)
    (i : Fin original.plans.length) (small : request.allowance ≤ 1) :
    Bounded ((PairedIncrementArea.total (DyadicPairedPrimitivePaths.increments
      (CommonRibbonRequest.sourceValues (evaluated.entries.get i).samples.source
        (evaluated.entries.get i).samples.otherSource)
      (original.depth + depth) 0 1)).sub
      (PairedIncrementArea.total (VertexTrace.increments (chartTrace (evaluated.entries.get i)) id)))
        (16 * request.allowance) := by
  let entry := evaluated.entries.get i
  have bounded := BlockBank.joined_total_accurate entry (CommonChartBlockComparison.blockBank entry) small
  rw [(CommonChartBlockComparison.blockBank entry).source.total_eq, entry.sourceBlocks_full,
    PairedParentCharts.chartDepth_eq original depth i] at bounded
  exact bounded

/-- Area transport uses the same source samples as the endpoint transport; its scale is the retained common-cover block
scale. -/
theorem Evaluation.parent_source_area_bound (evaluated : request.Evaluation)
    (i : Fin original.plans.length) (small : request.allowance ≤ 1) :
    normSq (PairedIncrementArea.area (DyadicPairedPrimitivePaths.increments
      (CommonRibbonRequest.sourceValues (evaluated.entries.get i).samples.source
        (evaluated.entries.get i).samples.otherSource)
      (original.depth + depth) 0 1) -
      PairedIncrementArea.area (VertexTrace.increments (chartTrace (evaluated.entries.get i)) id)) ≤
        CommonRequestedBoundary.joinedBlockScale
          (ChartParent original i).common * request.allowance := by
  let entry := evaluated.entries.get i
  have bounded := BlockBank.joined_source_bound entry (CommonChartBlockComparison.blockBank entry) small
  rw [(CommonChartBlockComparison.blockBank entry).source.area_eq, entry.sourceBlocks_full,
    PairedParentCharts.chartDepth_eq original depth i] at bounded
  exact bounded

/-- Assemble the raw source-to-parent-chart total error in the retained parent order. Connectors between parents are not
included in this estimate. -/
theorem Evaluation.source_parent_totals_bound (evaluated : request.Evaluation)
    (small : request.allowance ≤ 1) :
    Bounded ((PairedIncrementArea.total evaluated.sourcePaths.flatten).sub
      (PairedIncrementArea.total (List.ofFn (fun i : Fin original.plans.length =>
        VertexTrace.increments (chartTrace (evaluated.entries.get i)) id)).flatten))
      ((original.plans.length : Coordinate)^2 * (16 * request.allowance)) := by
  let pairs := List.ofFn (fun i : Fin original.plans.length =>
    (PairedIncrementArea.total (DyadicPairedPrimitivePaths.increments
      (CommonRibbonRequest.sourceValues (evaluated.entries.get i).samples.source
        (evaluated.entries.get i).samples.otherSource) (original.depth + depth) 0 1),
      PairedIncrementArea.total (VertexTrace.increments (chartTrace (evaluated.entries.get i)) id)))
  have errors : ∀ point ∈ pairs.map (fun pair => pair.1.sub pair.2),
      Bounded point (16 * request.allowance) := by
    intro point member
    obtain ⟨pair, inPairs, rfl⟩ := Map.mem_map.mp member
    obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp inPairs
    exact Evaluation.parent_source_total_bound
      evaluated i small
  have bound := PairedIncrementArea.total_bound
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Coordinate) ≤ 16)
      request.positive.le) errors
    (count := original.plans.length) (by
      rw [Map.length_map, OfFn.Basic.length_ofFn])
  rw [PairedIncrementComparison.total_differences] at bound
  rw [PairedAreaBlocks.total_flatten, PairedAreaBlocks.total_flatten]
  simp only [pairs, Evaluation.sourcePaths, OfFn.Basic.map_ofFn, -eq_self, -iff_self] at bound ⊢
  dsimp only [Function.comp_def] at bound ⊢
  exact bound

/-- A shared reading floor can satisfy several endpoint requests while preserving all their cap-polynomial values and
comparison indices. -/
theorem RegularEndpointRequest.atReadingFloor_bound (evaluated : request.Evaluation)
    (i j : Fin original.plans.length) (joined : EndpointJoin request i j)
    (error : Coordinate) (positive : 0 < error) (floor : Nat)
    (stage : Nat)
    (later : (RegularEndpointRequest.build evaluated i j joined error positive floor).index ≤ stage)
    (unramified : HyperellipticReciprocal.originOrder curve = 0) :
    let retained := Evaluation.atReadingFloor
      evaluated stage
    Bounded ((chartTrace (retained.entries.get j)).first.sub (chartTrace
      (retained.entries.get i)).last) error := by
  intro retained
  let next := RegularEndpointRequest.build retained i j joined error positive floor
  have same : next.index = (RegularEndpointRequest.build evaluated i j joined error positive floor).index := rfl
  exact RegularEndpointRequest.accurate next unramified
    (same.trans_le (later.trans
      (Evaluation.atReadingFloor_lastStage
      evaluated stage i)))
    (same.trans_le (later.trans
      (Evaluation.atReadingFloor_firstStage
      evaluated stage j)))

/-- Compute the needed reading floor and apply the endpoint bound on the reread bank. No caller later-stage inequalities
remain. -/
theorem RegularEndpointRequest.acquire_bound (evaluated : request.Evaluation)
    (i j : Fin original.plans.length) (joined : EndpointJoin request i j)
    (error : Coordinate) (positive : 0 < error) (floor : Nat)
    (unramified : HyperellipticReciprocal.originOrder curve = 0) :
    let planned := RegularEndpointRequest.build evaluated i j joined error positive floor
    let retained := Evaluation.atReadingFloor
      evaluated planned.index
    Bounded ((chartTrace (retained.entries.get j)).first.sub (chartTrace
      (retained.entries.get i)).last) error :=
  RegularEndpointRequest.atReadingFloor_bound
    evaluated i j joined error positive floor _ le_rfl unramified

/-- Root closure chooses the final endpoint request. Its internally raised reading floor makes the total of the unclosed
chart increments small. -/
theorem Evaluation.regularTrace_total_requested (evaluated : request.Evaluation)
    (present : 0 < original.plans.length)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)))
    {first last : Gaussian.Name.Basic.Named}
    (roots : PreparedRefinementRootChains.RootChain parents first last)
    (closed : start.coordinate = finish.coordinate)
    (returned : Gaussian.Equivalence.NamedEquivalent last first)
    (error : Coordinate) (positive : 0 < error) (floor : Nat)
    (unramified : HyperellipticReciprocal.originOrder curve = 0) :
    let joined := closingJoin request present chain roots closed returned
    let planned := RegularEndpointRequest.build evaluated _ _ joined error positive floor
    let retained := Evaluation.atReadingFloor
      evaluated planned.index
    Bounded (PairedIncrementArea.total (VertexTrace.increments (Evaluation.regularTrace retained) id))
      error := by
  intro joined planned retained
  have bounded :=
    RegularEndpointRequest.acquire_bound
    evaluated _ _ joined error positive floor unramified
  change Bounded ((chartTrace (retained.entries.get ⟨0, present⟩)).first.sub
    (chartTrace (retained.entries.get ⟨original.plans.length - 1, by omega0⟩)).last) error at bounded
  rw [Evaluation.regularTrace_increment_total retained, Evaluation.regularTrace_last retained present,
    Evaluation.regularTrace_first retained present]
  have reverse (a b : Gaussian) :
      Data.Gaussian.Basic.Canonical.normSq (a - b) = Data.Gaussian.Basic.Canonical.normSq (b - a) := by
    rw [show a - b = -(b - a) by ring1, Data.Gaussian.Basic.Canonical.normSq_neg]
  exact ⟨(reverse _ _).trans_le bounded.1, (reverse _ _).trans_le bounded.2⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentReadings
